{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-orphans #-} -- instance Diagnostic TcRnMessage

module GHC.Tc.Errors.Ppr (
    formatLevPolyErr
  , pprLevityPolyInType
  ) where

import GHC.Prelude

import GHC.Core.TyCo.Ppr (pprWithTYPE)
import GHC.Core.Type
import GHC.Tc.Errors.Types
import GHC.Types.Error
import GHC.Types.Var.Env (emptyTidyEnv)
import GHC.Driver.Flags
import GHC.Hs
import GHC.Utils.Outputable

instance Diagnostic TcRnMessage where
  diagnosticMessage = \case
    TcRnUnknownMessage m
      -> diagnosticMessage m
    TcLevityPolyInType ty prov (ErrInfo extra)
      -> mkDecorated [pprLevityPolyInType ty prov, extra]
    TcRnImplicitLift id_or_name errInfo
      -> mkDecorated [text "The variable" <+> quotes (ppr id_or_name) <+>
                      text "is implicitly lifted in the TH quotation"
                     , getErrInfo errInfo
                     ]
    TcRnUnusedPatternBinds bind
      -> mkDecorated [hang (text "This pattern-binding binds no variables:") 2 (ppr bind)]
    TcRnDodgyImports name
      -> mkDecorated [dodgy_msg (text "import") name (dodgy_msg_insert name :: IE GhcPs)]
    TcRnDodgyExports name
      -> mkDecorated [dodgy_msg (text "export") name (dodgy_msg_insert name :: IE GhcRn)]
    TcRnMissingImportList ie
      -> mkDecorated [ text "The import item" <+> quotes (ppr ie) <+>
                       text "does not have an explicit import list"
                     ]

  diagnosticReason = \case
    TcRnUnknownMessage m
      -> diagnosticReason m
    TcLevityPolyInType{}
      -> ErrorWithoutFlag
    TcRnImplicitLift{}
      -> WarningWithFlag Opt_WarnImplicitLift
    TcRnUnusedPatternBinds{}
      -> WarningWithFlag Opt_WarnUnusedPatternBinds
    TcRnDodgyImports{}
      -> WarningWithFlag Opt_WarnDodgyImports
    TcRnDodgyExports{}
      -> WarningWithFlag Opt_WarnDodgyExports
    TcRnMissingImportList{}
      -> WarningWithFlag Opt_WarnMissingImportList

  diagnosticHints = \case
    TcRnUnknownMessage m
      -> diagnosticHints m
    TcLevityPolyInType{}
      -> noHints
    TcRnImplicitLift{}
      -> noHints
    TcRnUnusedPatternBinds{}
      -> noHints
    TcRnDodgyImports{}
      -> noHints
    TcRnDodgyExports{}
      -> noHints
    TcRnMissingImportList{}
      -> noHints

dodgy_msg :: (Outputable a, Outputable b) => SDoc -> a -> b -> SDoc
dodgy_msg kind tc ie
  = sep [ text "The" <+> kind <+> text "item"
                     <+> quotes (ppr ie)
                <+> text "suggests that",
          quotes (ppr tc) <+> text "has (in-scope) constructors or class methods,",
          text "but it has none" ]

dodgy_msg_insert :: forall p . IdP (GhcPass p) -> IE (GhcPass p)
dodgy_msg_insert tc = IEThingAll noAnn ii
  where
    ii :: LIEWrappedName (IdP (GhcPass p))
    ii = noLocA (IEName $ noLocA tc)

formatLevPolyErr :: Type  -- levity-polymorphic type
                 -> SDoc
formatLevPolyErr ty
  = hang (text "A levity-polymorphic type is not allowed here:")
       2 (vcat [ text "Type:" <+> pprWithTYPE tidy_ty
               , text "Kind:" <+> pprWithTYPE tidy_ki ])
  where
    (tidy_env, tidy_ty) = tidyOpenType emptyTidyEnv ty
    tidy_ki             = tidyType tidy_env (tcTypeKind ty)

pprLevityPolyInType :: Type -> LevityCheckProvenance -> SDoc
pprLevityPolyInType ty prov =
  let extra = case prov of
        LevityCheckInBinder v
          -> text "In the type of binder" <+> quotes (ppr v)
        LevityCheckInVarType
          -> text "When trying to create a variable of type:" <+> ppr ty
        LevityCheckInWildcardPattern
          -> text "In a wildcard pattern"
        LevityCheckInUnboxedTuplePattern p
          -> text "In the type of an element of an unboxed tuple pattern:" $$ ppr p
        LevityCheckPatSynSig
          -> empty
        LevityCheckCmdStmt
          -> empty -- I (Richard E, Dec '16) have no idea what to say here
        LevityCheckMkCmdEnv id_var
          -> text "In the result of the function" <+> quotes (ppr id_var)
        LevityCheckDoCmd do_block
          -> text "In the do-command:" <+> ppr do_block
        LevityCheckDesugaringCmd cmd
          -> text "When desugaring the command:" <+> ppr cmd
        LevityCheckInCmd body
          -> text "In the command:" <+> ppr body
        LevityCheckInFunUse using
          -> text "In the result of a" <+> quotes (text "using") <+> text "function:" <+> ppr using
        LevityCheckInValidDataCon
          -> empty
        LevityCheckInValidClass
          -> empty
  in formatLevPolyErr ty $$ extra
