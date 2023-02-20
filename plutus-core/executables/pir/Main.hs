-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import PlutusCore qualified as PLC
import PlutusCore.Compiler qualified as PLC
import PlutusCore.Error (ParserErrorBundle (..))
import PlutusCore.Executable.Common hiding (runPrint)
import PlutusCore.Executable.Parsers
import PlutusCore.Quote (runQuoteT)
import PlutusIR as PIR
import PlutusIR.Analysis.RetainedSize qualified as PIR
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Core.Instance.Pretty ()
import PlutusIR.Core.Plated
import PlutusPrelude
import UntypedPlutusCore qualified as UPLC

import Control.Lens (coerced, (^..))
import Control.Monad.Trans.Except (runExcept)
import Control.Monad.Trans.Reader (runReader, runReaderT)
import Data.ByteString.Lazy.Char8 qualified as BSL
import Data.Csv qualified as Csv
import Data.IntMap qualified as IM
import Data.List (sortOn)
import Data.Text qualified as T
import Options.Applicative
import Text.Megaparsec (errorBundlePretty)


type PIRErrorWithProvenance = PIR.Error PLC.DefaultUni PLC.DefaultFun (PIR.Provenance ())

---------------- Types for command line options ----------------

-- | A specialised format type for PIR. We don't support deBruijn or named deBruijn for PIR.
data PirFormat = TextualPir | FlatNamed
instance Show PirFormat
    where show = \case { TextualPir  -> "textual"; FlatNamed -> "flat-named" }

data PirOptimiseOptions = PirOptimiseOptions Input PirFormat Output Format PrintMode

data AnalyseOptions = AnalyseOptions Input PirFormat Output -- Input is a program, output is text

data Language = PLC | UPLC
instance Show Language
    where show = \case { PLC  -> "plc"; UPLC -> "uplc" }

-- | Compilation options: target language, whether to optimise or not, input and output streams and types
data CompileOptions =
    CompileOptions Language
                   Bool   -- Optimise or not?
                   Bool   -- True -> just report if compilation was successful; False -> write output
                   Input
                   PirFormat
                   Output
                   Format
                   PrintMode

data Command = Analyse  AnalyseOptions
             | Compile  CompileOptions
             | Convert  ConvertOptions
             | Optimise PirOptimiseOptions
             | Print    PrintOptions


---------------- Option parsers ----------------

-- | Invert a switch: return False if the switch is supplied on the command
-- line, True otherwise.  This is used for command-line options to turn things
-- off.
switch' :: Mod FlagFields Bool -> Parser Bool
switch' = fmap not . switch

pirFormatHelp :: String
pirFormatHelp =
  "textual or flat-named (names)"

pirFormatReader :: String -> Maybe PirFormat
pirFormatReader =
    \case
         "textual"    -> Just TextualPir
         "flat-named" -> Just FlatNamed
         "flat"       -> Just FlatNamed
         _            -> Nothing

pInputFormat :: Parser PirFormat
pInputFormat = option (maybeReader pirFormatReader)
  (  long "if"
  <> long "input-format"
  <> metavar "PIR-FORMAT"
  <> value TextualPir
  <> showDefault
  <> help ("Input format: " ++ pirFormatHelp))

pPirOptimiseOptions :: Parser PirOptimiseOptions
pPirOptimiseOptions = PirOptimiseOptions <$> input <*> pInputFormat <*> output <*> outputformat <*> printmode

pAnalyseOptions :: Parser AnalyseOptions
pAnalyseOptions = AnalyseOptions <$> input <*> pInputFormat <*> output

languageReader :: String -> Maybe Language
languageReader =
    \case
         "plc"  -> Just PLC
         "uplc" -> Just UPLC
         _      -> Nothing

pLanguage :: Parser Language
pLanguage = option (maybeReader languageReader)
  (  long "language"
  <> short 'l'
  <> metavar "LANGUAGE"
  <> value UPLC
  <> showDefault
  <> help ("Target language: plc or uplc")
  )

pOptimise :: Parser Bool
pOptimise = switch'
            (  long "dont-optimise"
            <> long "dont-optimize"
            <> help ("Turn off optimisations")
            )

pJustTest :: Parser Bool
pJustTest = switch ( long "test"
                   <> help "Just report success or failure, don't produce an output file"
                   )

pCompileOptions :: Parser CompileOptions
pCompileOptions = CompileOptions
               <$> pLanguage
               <*> pOptimise
               <*> pJustTest
               <*> input
               <*> pInputFormat
               <*> output
               <*> outputformat
               <*> printmode

pPirOptions :: Parser Command
pPirOptions = hsubparser $
             command "analyse"
                  (info (Analyse <$> pAnalyseOptions) $
                   progDesc $
                   "Given a PIR program in flat format, deserialise and analyse the program, " <>
                   "looking for variables with the largest retained size.")
           <> command "compile"
                  (info (Compile <$> pCompileOptions) $
                   progDesc $
                   "Given a PIR program in flat format, deserialise it, " <>
                   "and test if it can be successfully compiled to PLC.")
           <> command "convert"
                  (info (Convert <$> convertOpts)
                   (progDesc $
                    "Convert a program between various formats" <>
                    "(only 'textual' (default) and 'flat-named' are available for PIR)."))
           <> command "optimise"
                  (info (Optimise <$> pPirOptimiseOptions)
                   (progDesc "Run the PIR optimisation pipeline on the input."))
           <> command "optimize"
                  (info (Optimise <$> pPirOptimiseOptions)
                   (progDesc "Run the PIR optimisation pipeline on the input."))
           <> command "print"
                  (info (Print <$> printOpts) $
                 progDesc $
                   "Given a PIR program in flat format, " <>
                   "deserialise it and print it out textually.")


-- | Load a PIR program (in either textual of flat-named format)
getPirProgram ::
    PirFormat ->
    Input ->
    IO (PirProg PLC.SrcSpan)
getPirProgram fmt inp =
    case fmt of
        TextualPir -> snd <$> parseInput inp
        FlatNamed -> do
            prog <- loadTplcASTfromFlat Named inp  :: IO (PirProg ())
            -- No source locations in Flat, so we have to make them up.
            return $ topSrcSpan <$ prog


---------------- Compilation ----------------

compileToPlc :: Bool -> PirProg () -> Either PIRErrorWithProvenance (PlcTerm (PIR.Provenance ()))
compileToPlc optimise (PIR.Program _ pirT) = do
    plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
    let pirCtx = defaultCompilationCtx plcTcConfig
    runExcept $ flip runReaderT pirCtx $ runQuoteT $ PIR.compileTerm pirT
  where
    defaultCompilationCtx :: PLC.TypeCheckConfig PLC.DefaultUni PLC.DefaultFun
      -> PIR.CompilationCtx PLC.DefaultUni PLC.DefaultFun a
    defaultCompilationCtx plcTcConfig =
      PIR.toDefaultCompilationCtx plcTcConfig &
         PIR.ccOpts . PIR.coOptimize .~ optimise

compileToUplc :: Bool -> PlcProg () -> UplcProg ()
compileToUplc optimise plcProg =
    let plcCompilerOpts =
            if optimise
            then PLC.defaultCompilationOpts
            else PLC.defaultCompilationOpts & PLC.coSimplifyOpts . UPLC.soMaxSimplifierIterations .~ 0
    in flip runReader plcCompilerOpts $ runQuoteT $ PLC.compileProgram plcProg

loadPirAndCompile :: CompileOptions -> IO ()
loadPirAndCompile (CompileOptions language optimise test inp ifmt outp ofmt mode)  = do
    pirProg <- getPirProgram ifmt inp :: IO (PirProg PLC.SrcSpan)
    if test then putStrLn "!!! Compiling" else pure ()
    -- Now compile to plc, maybe optimising
    case compileToPlc optimise (() <$ pirProg) of
      Left pirError -> error $ show pirError
      Right plcTerm ->
          let plcProg = PLC.Program () version (() <$ plcTerm)
                  where version = PLC.defaultVersion
          in case language of
            PLC  -> if test
                    then putStrLn "!!! Compilation successful"
                    else writeProgram outp ofmt mode plcProg
            UPLC -> do  -- compile the PLC to UPLC
              let uplcProg = compileToUplc optimise plcProg
              if test
              then putStrLn "!!! Compilation successful"
              else writeProgram outp ofmt mode uplcProg


---------------- Optimisation ----------------

doOptimisations :: PirTerm PLC.SrcSpan -> Either PIRErrorWithProvenance (PirTerm ())
doOptimisations term = do
  plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
  let ctx = PIR.toDefaultCompilationCtx plcTcConfig
  let term' = (PIR.Original ()) <$ term
  opt <- runExcept $ flip runReaderT ctx $ runQuoteT $ PIR.simplifyTerm term'
  pure $ (() <$ opt)

-- | Run the PIR optimisations
runOptimisations:: PirOptimiseOptions -> IO ()
runOptimisations (PirOptimiseOptions inp ifmt outp ofmt mode) = do
  Program _ term <- getPirProgram ifmt inp :: IO (PirProg PLC.SrcSpan)
  case doOptimisations term of
    Left e  -> error $ show e
    Right t -> writeProgram outp ofmt mode (Program () t)


---------------- Analysis ----------------

-- | a csv-outputtable record row of {name,unique,size}
data RetentionRecord = RetentionRecord { name :: T.Text, unique :: Int, size :: PIR.Size}
    deriving stock (Generic, Show)
    deriving anyclass Csv.ToNamedRecord
    deriving anyclass Csv.DefaultOrdered
deriving newtype instance Csv.ToField PIR.Size

loadPirAndAnalyse :: AnalyseOptions -> IO ()
loadPirAndAnalyse (AnalyseOptions inp ifmt outp) = do
    -- load pir and make sure that it is globally unique (required for retained size)
    PIR.Program _ pirT <- PLC.runQuote . PLC.rename <$> getPirProgram ifmt inp
    putStrLn "!!! Analysing for retention"
    let
        -- all the variable names (tynames coerced to names)
        names = pirT ^.. termSubtermsDeep.termBindings.bindingNames ++
                pirT ^.. termSubtermsDeep.termBindings.bindingTyNames.coerced
        -- a helper lookup table of uniques to their textual representation
        nameTable :: IM.IntMap T.Text
        nameTable = IM.fromList [(coerce $ _nameUnique n , _nameText n) | n <- names]

        -- build the retentionMap
        retentionMap = PIR.termRetentionMap def pirT
        -- sort the map by decreasing retained size
        sortedRetained = sortOn (negate . snd) $ IM.assocs retentionMap

        -- change uniques to texts and use csv-outputtable records
        sortedRecords :: [RetentionRecord]
        sortedRecords =
          sortedRetained <&> \(i, s) ->
            RetentionRecord (IM.findWithDefault "given key is not in map" i nameTable) i s

    -- encode to csv and output it
    Csv.encodeDefaultOrderedByName sortedRecords &
        case outp of
            FileOutput path -> BSL.writeFile path
            StdOutput       -> BSL.putStr


---------------- Parse and print a PIR source file ----------------
-- This option for PIR source file does NOT check for @UniqueError@'s.
-- Only the print option for PLC or UPLC files check for them.

runPrint :: PrintOptions -> IO ()
runPrint (PrintOptions iospec _mode) = do
    let inputPath = inputSpec iospec
    contents <- getInput inputPath
    -- parse the program
    case parseNamedProgram (show inputPath) contents of
      -- when fail, pretty print the parse errors.
      Left (ParseErrorB err) ->
          errorWithoutStackTrace $ errorBundlePretty err
      -- otherwise,
      Right (p::PirProg PLC.SrcSpan) -> do
        -- pretty print the program. Print mode may be added later on.
        let
            printed :: String
            printed = show $ pretty p
        case outputSpec iospec of
            FileOutput path -> writeFile path printed
            StdOutput       -> putStrLn printed


---------------- Main ----------------

main :: IO ()
main = do
    comm <- customExecParser (prefs showHelpOnEmpty) infoOpts
    case comm of
        Analyse  opts -> loadPirAndAnalyse opts
        Compile  opts -> loadPirAndCompile opts
        Convert  opts -> runConvert @PirProg opts
        Optimise opts -> runOptimisations opts
        Print    opts -> runPrint opts
  where
    infoOpts =
      info (pPirOptions <**> helper)
           ( fullDesc
           <> header "PIR tool"
           <> progDesc ("This program provides a number of utilities for dealing with "
           <> "PIR programs, including printing, analysis, optimisation, and compilation to UPLC and PLC."))

