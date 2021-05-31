{-# LANGUAGE ExistentialQuantification #-}

module GHC.HsToCore.Errors.Types where

import Data.Typeable

import GHC.Prelude

import GHC.Core (CoreRule, CoreExpr, RuleName)
import GHC.Core.DataCon
import GHC.Core.Type
import GHC.Driver.Session
import GHC.Hs
import GHC.Types.Error
import GHC.Types.Id
import GHC.Types.Name (Name)
import qualified GHC.LanguageExtensions as LangExt
import GHC.HsToCore.Pmc.Solver.Types
import GHC.Types.Basic (Activation)
import GHC.Types.ForeignCall
import GHC.Utils.Outputable

newtype MinBound = MinBound Integer
newtype MaxBound = MaxBound Integer
type MaxUncoveredPatterns = Int
type MaxPmCheckModels = Int

-- | Diagnostics messages emitted during desugaring.
data DsMessage
  -- | Simply wraps a generic 'Diagnostic' message.
  = forall a. (Diagnostic a, Typeable a) => DsUnknownMessage a

  | DsEmptyEnumeration

  | DsIdentitiesFound !Id   -- The conversion function
                      !Type -- The type of conversion

  | DsOverflowedLiterals !Integer
                         !Name
                         !(Maybe (MinBound, MaxBound))
                         !NegLiteralExtEnabled

  -- FIXME(adn) Use a proper type instead of 'SDoc', but unfortunately
  -- 'SrcInfo' gives us an 'SDoc' to begin with.
  | DsRedundantBangPatterns !(HsMatchContext GhcRn) !SDoc

  -- FIXME(adn) Use a proper type instead of 'SDoc', but unfortunately
  -- 'SrcInfo' gives us an 'SDoc' to begin with.
  | DsOverlappingPatterns !(HsMatchContext GhcRn) !SDoc

  -- FIXME(adn) Use a proper type instead of 'SDoc'
  | DsInaccessibleRhs !(HsMatchContext GhcRn) !SDoc

  | DsMaxPmCheckModelsReached !MaxPmCheckModels

  | DsNonExhaustivePatterns !(HsMatchContext GhcRn)
                            !ExhaustivityCheckType
                            !MaxUncoveredPatterns
                            [Id]
                            [Nabla]

  | DsTopLevelBindsNotAllowed !BindsType !(HsBindLR GhcTc GhcTc)

  | DsUselessSpecialiseForClassMethodSelector !Id

  | DsUselessSpecialiseForNoInlineFunction !Id

  | DsMultiplicityCoercionsNotSupported

  | DsOrphanRule !CoreRule

  | DsRuleLhsTooComplicated !CoreExpr !CoreExpr

  | DsRuleIgnoredDueToConstructor !DataCon

  | DsRuleBindersNotBound ![Var]
                          -- ^ The list of unbound binders
                          ![Var]
                          -- ^ The original binders
                          !CoreExpr
                          -- ^ The original LHS
                          !CoreExpr
                          -- ^ The optimised LHS

  | DsMultipleConForNewtype [LocatedN Name]

  | DsLazyPatCantBindVarsOfUnliftedType [Var]

  | DsNotYetHandledByTH !ThRejectionReason

  | DsAggregatedViewExpressions [[LHsExpr GhcTc]]

  | DsUnbangedStrictPatterns !(HsBindLR GhcTc GhcTc)

  | DsCannotMixPolyAndUnliftedBindings !(HsBindLR GhcTc GhcTc)

  | DsInvalidInstantiationDictAtType !Type

  | DsWrongDoBind !(LHsExpr GhcTc) !Type

  | DsUnusedDoBind !(LHsExpr GhcTc) !Type

  | DsRecBindsNotAllowedForUnliftedTys ![LHsBindLR GhcTc GhcTc]

  -- FIXME(adn) Unfortunately the first argument is an opaque 'ty' with an
  -- 'Outputable' constraint because this messages is emitted from 'GHC.HsToCore.Expr.checkLevPolyArgs'
  -- which gets passed a completely polymorphic, 'Outputable' type.
  | forall ty. Outputable ty => DsCannotUseFunWithPolyArgs !ty !Type ![Type]

  | DsRuleMightInlineFirst !RuleName !Var !Activation

  | DsAnotherRuleMightFireFirst !RuleName
                                !RuleName -- the \"bad\" rule
                                !Var

  | DsLevityPolyInExpr !CoreExpr !LevityExprProvenance

  | DsLevityPolyInType !Type !LevityCheckProvenance

-- The positional number of the argument for an expression (first, second, third, etc)
newtype DsArgNum = DsArgNum Int

-- | Where the levity checking for the input type originated
data LevityCheckProvenance
  = LevityCheckInVarType
  | LevityCheckInBinder !Var
  | LevityCheckInWildcardPattern
  | LevityCheckInUnboxedTuplePattern !(Pat GhcTc)
  | LevityCheckGenSig
  | LevityCheckCmdStmt
  | LevityCheckMkCmdEnv !Var
  | LevityCheckDoCmd !(HsCmd GhcTc)
  | LevityCheckDesugaringCmd !(LHsCmd GhcTc)
  | LevityCheckInCmd !(LHsCmd GhcTc)
  | LevityCheckInFunUse !(LHsExpr GhcTc)
  | LevityCheckInValidDataCon
  | LevityCheckInValidClass

-- | Where the levity checking for the expression originated
data LevityExprProvenance
  = LevityCheckHsExpr !(HsExpr GhcTc)
  | LevityCheckWpFun !SDoc -- FIXME(adn) Alas 'WpFun' gives us an SDoc here.
  | LevityCheckInSyntaxExpr !DsArgNum !(HsExpr GhcTc)

-- | Why TemplateHaskell rejected the splice. Used in the 'DsNotYetHandledByTH'
-- constructor of a 'DsMessage'.
data ThRejectionReason
  = ThAmbiguousRecordUpdates !(HsRecUpdField GhcRn)
  | ThAbstractClosedTypeFamily !(LFamilyDecl GhcRn)
  | ThForeignLabel !CLabelString
  | ThForeignExport !(LForeignDecl GhcRn)
  | ThMinimalPragmas
  | ThSCCPragmas
  | ThNoUserInline
  | ThExoticFormOfType !(HsType GhcRn)
  | ThAmbiguousRecordSelectors !(HsExpr GhcRn)
  | ThMonadComprehensionSyntax !(HsExpr GhcRn)
  | ThCostCentres !(HsExpr GhcRn)
  | ThExpressionForm !(HsExpr GhcRn)
  | ThExoticStatement [Stmt GhcRn (LHsExpr GhcRn)]
  | ThExoticLiteral !(HsLit GhcRn)
  | ThExoticPattern !(Pat GhcRn)
  | ThGuardedLambdas !(Match GhcRn (LHsExpr GhcRn))
  | ThNegativeOverloadedPatterns !(Pat GhcRn)
  | ThHaddockDocumentation
  | ThWarningAndDeprecationPragmas [LIdP GhcRn]
  | ThDefaultDeclarations !(DefaultDecl GhcRn)
  | ThSplicesWithinDeclBrackets

data NegLiteralExtEnabled
  = YesUsingNegLiterals
  | NotUsingNegLiterals

negLiteralExtEnabled :: DynFlags -> NegLiteralExtEnabled
negLiteralExtEnabled dflags =
 if (xopt LangExt.NegativeLiterals dflags) then YesUsingNegLiterals else NotUsingNegLiterals

newtype ExhaustivityCheckType = ExhaustivityCheckType (Maybe WarningFlag)

data BindsType
  = UnliftedTypeBinds
  | StrictBinds
