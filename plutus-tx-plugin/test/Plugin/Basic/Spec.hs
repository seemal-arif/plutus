-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fmax-simplifier-iterations=0 #-}
{-# OPTIONS_GHC -fno-specialise -O0 #-}
{-# OPTIONS_GHC -fforce-recomp #-}

module Plugin.Basic.Spec where

import Test.Tasty.Extras

import PlutusCore.Test
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Plugin
import PlutusTx.Prelude as P
import PlutusTx.Test

import Data.Proxy
import PlutusTx.Builtins qualified as Builtin
import Prelude hiding ((+))


basic :: TestNested
basic = testNested "Basic" [
    -- goldenPir "letOverApp" monoId
    goldenPir "letApp" letApp
    , goldenPir "letIdFunForall" letIdFunForall
    , goldenPir "letIdFunForallMulti" letIdFunForallMulti
    , goldenPir "letIdFunForallMultiNotSat" letIdFunForallMultiNotSat
    , goldenPir "letFunEg2" letFun2
    , goldenPir "letFunInFunAllMulti" letFunInFunAllMulti
    , goldenPir "letFunInFunMulti" letFunInFunMulti
    , goldenPir "letFunInFunMultiFullyApplied" letFunInFunMultiFullyApplied
    , goldenPir "letFunForall" letFunForall
    , goldenPir "letAppMulti" letAppMulti
    , goldenPir "letOverAppMulti" letOverAppMulti
    , goldenPir "letOverAppType" letOverAppType
    , goldenPir "letFunConstMulti" letFunConstMulti
    , goldenPir "cl1" cl1
    , goldenPir "cl2" cl2
    , goldenPir "cl3" cl3
    , goldenPir "nonpure" nonpure
    , goldenUPlc "letApp" letApp
    , goldenUPlc "letIdFunForall" letIdFunForall
    , goldenUPlc "letIdFunForallMulti" letIdFunForallMulti
    , goldenUPlc "letIdFunForallMultiNotSat" letIdFunForallMultiNotSat
    , goldenUPlc "letFunEg2" letFun2
    , goldenUPlc "letFunInFunAllMulti" letFunInFunAllMulti
    , goldenUPlc "letFunInFunMulti" letFunInFunMulti
    , goldenUPlc "letFunInFunMultiFullyApplied" letFunInFunMultiFullyApplied
    , goldenUPlc "letFunForall" letFunForall
    , goldenUPlc "letAppMulti" letAppMulti
    , goldenUPlc "letOverAppMulti" letOverAppMulti
    , goldenUPlc "letFunConstMulti" letFunConstMulti
    , goldenUPlc "cl1" cl1
    , goldenUPlc "cl2" cl2
    , goldenUPlc "cl3" cl3

--   , goldenPir "monoK" monoK
--   , goldenPir "letFun" letFun
--   , goldenPir "nonstrictLet" nonstrictLet
--   , goldenPir "strictLet" strictLet
--   , goldenPir "strictMultiLet" strictMultiLet
--   , goldenPir "strictLetRec" strictLetRec
--   -- must keep the scrutinee as it evaluates to error
--   , goldenPir "ifOpt" ifOpt
--   -- should fail
--   , goldenUEval "ifOptEval" [ifOpt]
--   , goldenPir "monadicDo" monadicDo
--   , goldenPir "patternMatchDo" patternMatchDo
--   , goldenUPlcCatch "patternMatchFailure" patternMatchFailure
  ]

letOverAppType :: CompiledCode Integer
letOverAppType = plc (Proxy @"letOverAppType") (
    let
        idFun :: forall a . a -> a
        {-# NOINLINE idFun #-}
        idFun = \x -> x
        funApp :: Integer -> Integer
        {-# NOINLINE funApp #-}
        funApp = idFun @Integer
        k :: forall a . a -> a
        {-# NOINLINE k #-}
        k = idFun
    in k @Integer (k @(Integer -> Integer) funApp 3)
    )

nonpure :: CompiledCode Integer
nonpure = plc (Proxy @"nonpure") (
    let ~y = trace "hello" 1
        !x = y -- so it looks small enough to inline
    in Builtin.addInteger x x
    )

cl1 :: CompiledCode (Integer -> Integer -> Integer -> Integer)
cl1 = plc (Proxy @"cl1") (
    \x y z -> x
    )

cl2 :: CompiledCode (Integer -> Integer -> Integer -> (Integer -> Integer))
cl2 = plc (Proxy @"cl1") (
    \x y z -> (\k -> x)
    )

cl3 :: CompiledCode (Integer -> Integer -> Integer -> Integer )
cl3 = plc (Proxy @"cl1") (
    \x y z -> ((\k -> x) 3)
    )

cl4 :: forall a . CompiledCode (a -> a -> a -> a )
cl4 = plc (Proxy @"cl1") (
    \x y z -> x
    )


letApp :: CompiledCode Integer
{-# NOINLINE letApp #-}
letApp = plc (Proxy @"letApp") (
    let appNum :: Integer
        {-# NOINLINE appNum #-}
        appNum = 4
        funApp :: Integer -> Integer
        {-# NOINLINE funApp #-}
        funApp = (\x y -> Builtin.addInteger x y) appNum
    in funApp 5
    )

letFun2 :: CompiledCode Integer
{-# NOINLINE letFun2 #-}
letFun2 = plc (Proxy @"monoId") (
    let idFun :: Integer -> Integer
        {-# NOINLINE idFun #-}
        idFun = \x -> x
        funApp :: Integer -> (Integer -> Integer)
        {-# NOINLINE funApp #-}
        funApp = \x -> idFun
    in funApp 5 6
    )

letIdFunForallMulti :: CompiledCode Integer
{-# NOINLINE letIdFunForallMulti #-}
letIdFunForallMulti = plc (Proxy @"letIdFunForallMulti") (
    let idFun :: forall a . a -> a
        {-# NOINLINE idFun #-}
        idFun = \x -> x
    in Builtin.addInteger (idFun @Integer 3) (idFun @Integer 3)
    )

letIdFunForall :: CompiledCode Integer
{-# NOINLINE letIdFunForall #-}
letIdFunForall = plc (Proxy @"letIdFunForall") (
    let idFun :: forall a . a -> a
        {-# NOINLINE idFun #-}
        idFun = \x -> x
    in idFun @Integer 3--[Builtin.addInteger [idFun @Integer 3] [idFun @Integer 3]]
    )

letIdFunForallMultiNotSat :: CompiledCode (Integer -> Integer)
letIdFunForallMultiNotSat = plc (Proxy @"letIdFunForallMultiNotSat") (
    let idFun :: forall a . a -> a
        {-# NOINLINE idFun #-}
        idFun = \x -> x
    in (idFun @(Integer-> Integer)) (idFun @Integer)
    )


letFunInFunAllMulti :: CompiledCode ((Integer -> Integer))
letFunInFunAllMulti = plc (Proxy @"letFunInFunAllMulti") (
    let
        idFun :: Integer -> Integer
        {-# NOINLINE idFun #-}
        idFun x = x
        g :: (Integer -> Integer) -> (Integer -> Integer)
        {-# NOINLINE g #-}
        g y = idFun
        k :: (Integer -> Integer) -> (Integer -> Integer)
        {-# NOINLINE k #-}
        k = g
    in k idFun
    )

letFunInFunMulti :: CompiledCode ((Integer -> Integer))
letFunInFunMulti = plc (Proxy @"letFunInFunMulti") (
    let
        idFun :: Integer -> Integer
        {-# NOINLINE idFun #-}
        idFun x = x
        g :: (Integer -> Integer) -> (Integer -> Integer)
        {-# NOINLINE g #-}
        g y = idFun
    in g idFun
    )

letFunInFunMultiFullyApplied :: CompiledCode Integer
letFunInFunMultiFullyApplied = plc (Proxy @"letFunInFunMultiFullyApplied") (
    let
        idFun :: Integer -> Integer
        {-# NOINLINE idFun #-}
        idFun x = x
        g :: (Integer -> Integer) -> (Integer -> Integer)
        {-# NOINLINE g #-}
        g y = idFun
    in g idFun 1
    )

letFunForall :: CompiledCode Integer
letFunForall = plc (Proxy @"letFunForall") (
    let
        idFun :: forall a. a -> a
        {-# NOINLINE idFun #-}
        idFun x = x
        g :: (Integer -> Integer) -> (Integer -> Integer)
        {-# NOINLINE g #-}
        g y = idFun
    in g idFun 1
    )

letAppMulti :: CompiledCode Integer
letAppMulti = plc (Proxy @"letAppMulti") (
    let
        appNum :: Integer
        {-# NOINLINE  appNum #-}
        appNum = 4
        funApp :: Integer -> Integer
        {-# NOINLINE funApp #-}
        funApp x = Builtin.addInteger appNum x
        k :: Integer -> Integer
        {-# NOINLINE k #-}
        k = funApp
    in k appNum
    )

letOverAppMulti :: CompiledCode Integer
letOverAppMulti = plc (Proxy @"letOverAppMulti") (
    let
        idFun :: Integer -> Integer
        {-# NOINLINE idFun #-}
        idFun y = y
        funApp :: (Integer -> Integer) -> (Integer -> Integer)
        {-# NOINLINE funApp #-}
        funApp x = idFun
        k :: (Integer -> Integer) -> (Integer -> Integer)
        {-# NOINLINE k #-}
        k = funApp
    in k (k idFun) 6
    )

letFunConstMulti :: CompiledCode (Integer -> Integer)
letFunConstMulti = plc (Proxy @"letFunConstMulti") (
    let
        constFun :: Integer -> Integer -> Integer
        {-# NOINLINE constFun #-}
        constFun x y = x
    in constFun (constFun 3 5)
    )

monoK :: CompiledCode (Integer -> Integer -> Integer)
monoK = plc (Proxy @"monoK") (\(i :: Integer) -> \(_ :: Integer) -> i)

-- GHC actually turns this into a lambda for us, try and make one that stays a let
letFun :: CompiledCode (Integer -> Integer -> Bool)
letFun = plc (Proxy @"letFun") (\(x::Integer) (y::Integer) -> let f z = Builtins.equalsInteger x z in f y)

nonstrictLet :: CompiledCode (Integer -> Integer -> Integer)
nonstrictLet = plc (Proxy @"strictLet") (\(x::Integer) (y::Integer) -> let z = Builtins.addInteger x y in Builtins.addInteger z z)

-- GHC turns strict let-bindings into case expressions, which we correctly turn into strict let-bindings
strictLet :: CompiledCode (Integer -> Integer -> Integer)
strictLet = plc (Proxy @"strictLet") (\(x::Integer) (y::Integer) -> let !z = Builtins.addInteger x y in Builtins.addInteger z z)

strictMultiLet :: CompiledCode (Integer -> Integer -> Integer)
strictMultiLet = plc (Proxy @"strictLet") (\(x::Integer) (y::Integer) -> let !z = Builtins.addInteger x y; !q = Builtins.addInteger z z; in Builtins.addInteger q q)

-- Here we see the wrinkles of GHC's codegen: GHC creates let-bindings for the recursion, with _nested_ case expressions for the strictness.
-- So we get non-strict external bindings for z and q, and inside that we get strict bindings corresponding to the case expressions.
strictLetRec :: CompiledCode (Integer -> Integer -> Integer)
strictLetRec = plc (Proxy @"strictLetRec") (\(x::Integer) (y::Integer) -> let !z = Builtins.addInteger x q; !q = Builtins.addInteger y z in Builtins.addInteger z z)

ifOpt :: CompiledCode Integer
ifOpt = plc (Proxy @"ifOpt") (if ((1 `Builtins.divideInteger` 0) `Builtins.equalsInteger` 0) then 1 else 1)

-- TODO: It's pretty questionable that this works at all! It's actually using 'Monad' from 'base',
-- since that's what 'do' notation is hard-coded to use, and it just happens that it's all inlinable
-- enough to work...
-- Test what basic do-notation looks like (should just be a bunch of calls to '>>=')
monadicDo :: CompiledCode (Maybe Integer -> Maybe Integer -> Maybe Integer)
monadicDo = plc (Proxy @"monadicDo") (\(x :: Maybe Integer) (y:: Maybe Integer) -> do
    x' <- x
    y' <- y
    P.pure (x' `Builtins.addInteger` y'))

-- Irrefutable match in a do block
patternMatchDo :: CompiledCode (Maybe (Integer, Integer) -> Maybe Integer -> Maybe Integer)
patternMatchDo = plc (Proxy @"patternMatchDo") (\(x :: Maybe (Integer, Integer)) (y:: Maybe Integer) -> do
    (x1, x2) <- x
    y' <- y
    P.pure (x1 `Builtins.addInteger` x2 `Builtins.addInteger` y'))

-- Should fail, since it'll call 'MonadFail.fail' with a String, which won't work
patternMatchFailure :: CompiledCode (Maybe (Maybe Integer) -> Maybe Integer -> Maybe Integer)
patternMatchFailure = plc (Proxy @"patternMatchFailure") (\(x :: Maybe (Maybe Integer)) (y:: Maybe Integer) -> do
    Just x' <- x
    y' <- y
    P.pure (x' `Builtins.addInteger` y'))
