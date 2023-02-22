{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Builtin.KnownTypeAstInstance where

import PlutusCore.Builtin.Emitter
import PlutusCore.Builtin.KnownKind
import PlutusCore.Builtin.KnownTypeAst
import PlutusCore.Builtin.Meaning
import PlutusCore.Builtin.Polymorphism
import PlutusCore.Builtin.TypeScheme
import PlutusCore.Core
import PlutusCore.Evaluation.Result
import PlutusCore.MkPlc hiding (error)
import PlutusCore.Name

import Data.Proxy
import Data.Some.GADT qualified as GADT
import Data.Text qualified as Text
import Data.Type.Bool
import GHC.TypeLits
import Universe

type instance DeferredType = Type

argProxy :: TypeScheme val (arg ': args) res -> Proxy arg
argProxy _ = Proxy

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
-- Basically, a map from the PHOAS representation to the FOAS one.
typeSchemeToType :: TypeScheme val args res -> Type TyName (UniOf val) ()
typeSchemeToType sch@TypeSchemeResult       = toTypeAst sch
typeSchemeToType sch@(TypeSchemeArrow schB) =
    TyFun () (toTypeAst $ argProxy sch) $ typeSchemeToType schB
typeSchemeToType (TypeSchemeAll proxy schK) = case proxy of
    (_ :: Proxy '(text, uniq, kind)) ->
        let text = Text.pack $ symbolVal @text Proxy
            uniq = fromIntegral $ natVal @uniq Proxy
            a    = TyName $ Name text $ Unique uniq
        in TyForall () a (demoteKind $ knownKind @kind) $ typeSchemeToType schK

-- | Get the type of a built-in function.
typeOfBuiltinFunction
    :: forall uni fun. ToBuiltinMeaning uni fun
    => BuiltinVersion fun -> fun -> Type TyName uni ()
typeOfBuiltinFunction ver fun =
    case toBuiltinMeaning @_ @_ @(Term TyName Name uni fun ()) ver fun of
        BuiltinMeaning sch _ _ -> typeSchemeToType sch

instance KnownTypeAst uni a => KnownTypeAst uni (EvaluationResult a) where
    type IsBuiltin (EvaluationResult a) = 'False
    type ToHoles (EvaluationResult a) = '[TypeHole a]
    type ToBinds (EvaluationResult a) = ToBinds a
    toTypeAst _ = toTypeAst $ Proxy @a

instance KnownTypeAst uni a => KnownTypeAst uni (Emitter a) where
    type IsBuiltin (Emitter a) = 'False
    type ToHoles (Emitter a) = '[TypeHole a]
    type ToBinds (Emitter a) = ToBinds a
    toTypeAst _ = toTypeAst $ Proxy @a

instance KnownTypeAst uni rep => KnownTypeAst uni (SomeConstant uni rep) where
    type IsBuiltin (SomeConstant uni rep) = 'False
    type ToHoles (SomeConstant _ rep) = '[RepHole rep]
    type ToBinds (SomeConstant _ rep) = ToBinds rep
    toTypeAst _ = toTypeAst $ Proxy @rep

instance KnownTypeAst uni rep => KnownTypeAst uni (Opaque val rep) where
    type IsBuiltin (Opaque val rep) = 'False
    type ToHoles (Opaque _ rep) = '[RepHole rep]
    type ToBinds (Opaque _ rep) = ToBinds rep
    toTypeAst _ = toTypeAst $ Proxy @rep

toTyNameAst
    :: forall text uniq. (KnownSymbol text, KnownNat uniq)
    => Proxy ('TyNameRep text uniq) -> TyName
toTyNameAst _ =
    TyName $ Name
        (Text.pack $ symbolVal @text Proxy)
        (Unique . fromIntegral $ natVal @uniq Proxy)

instance uni `Contains` f => KnownTypeAst uni (BuiltinHead f) where
    type IsBuiltin (BuiltinHead f) = 'True
    type ToHoles (BuiltinHead f) = '[]
    type ToBinds (BuiltinHead f) = '[]
    toTypeAst _ = mkTyBuiltin @_ @f ()

instance (KnownTypeAst uni a, KnownTypeAst uni b) => KnownTypeAst uni (a -> b) where
    type IsBuiltin (a -> b) = 'False
    type ToHoles (a -> b) = '[TypeHole a, TypeHole b]
    type ToBinds (a -> b) = Merge (ToBinds a) (ToBinds b)
    toTypeAst _ = TyFun () (toTypeAst $ Proxy @a) (toTypeAst $ Proxy @b)

instance (name ~ 'TyNameRep text uniq, KnownSymbol text, KnownNat uniq) =>
            KnownTypeAst uni (TyVarRep name) where
    type IsBuiltin (TyVarRep name) = 'False
    type ToHoles (TyVarRep name) = '[]
    type ToBinds (TyVarRep name) = '[ 'GADT.Some name ]
    toTypeAst _ = TyVar () . toTyNameAst $ Proxy @('TyNameRep text uniq)

instance (KnownTypeAst uni fun, KnownTypeAst uni arg) => KnownTypeAst uni (TyAppRep fun arg) where
    type IsBuiltin (TyAppRep fun arg) = IsBuiltin fun && IsBuiltin arg
    type ToHoles (TyAppRep fun arg) = '[RepHole fun, RepHole arg]
    type ToBinds (TyAppRep fun arg) = Merge (ToBinds fun) (ToBinds arg)
    toTypeAst _ = TyApp () (toTypeAst $ Proxy @fun) (toTypeAst $ Proxy @arg)

instance
        ( name ~ 'TyNameRep @kind text uniq, KnownSymbol text, KnownNat uniq
        , KnownKind kind, KnownTypeAst uni a
        ) => KnownTypeAst uni (TyForallRep name a) where
    type IsBuiltin (TyForallRep name a) = 'False
    type ToHoles (TyForallRep name a) = '[RepHole a]
    type ToBinds (TyForallRep name a) = Delete ('GADT.Some name) (ToBinds a)
    toTypeAst _ =
        TyForall ()
            (toTyNameAst $ Proxy @('TyNameRep text uniq))
            (demoteKind $ knownKind @kind)
            (toTypeAst $ Proxy @a)
