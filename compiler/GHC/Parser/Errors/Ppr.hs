{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -fno-warn-orphans #-} -- instance Diagnostic PsMessage

module GHC.Parser.Errors.Ppr where

import GHC.Prelude
import GHC.Driver.Flags
import GHC.Parser.Errors.Types
import GHC.Parser.Types
import GHC.Types.Basic
import GHC.Types.Error
import GHC.Types.Hint.Ppr (perhapsAsPat)
import GHC.Types.SrcLoc
import GHC.Types.Name.Reader (opIsAt, starInfo, rdrNameOcc, mkUnqual)
import GHC.Types.Name.Occurrence (isSymOcc, occNameFS, varName)
import GHC.Utils.Outputable
import GHC.Utils.Misc
import GHC.Data.FastString
import GHC.Data.Maybe (catMaybes)
import GHC.Hs.Expr (prependQualified,HsExpr(..))
import GHC.Hs.Type (pprLHsContext)
import GHC.Builtin.Names (allNameStrings)
import GHC.Builtin.Types (filterCTuple)
import qualified GHC.LanguageExtensions as LangExt


instance Diagnostic PsMessage where
  diagnosticMessage = \case
    PsUnknownMessage m
      -> diagnosticMessage m

    PsWarnHaddockInvalidPos
       -> mkSimpleDecorated $ text "A Haddock comment cannot appear in this position and will be ignored."
    PsWarnHaddockIgnoreMulti
       -> mkSimpleDecorated $
            text "Multiple Haddock comments for a single entity are not allowed." $$
            text "The extraneous comment will be ignored."
    PsWarnTab tc
      -> mkSimpleDecorated $
           text "Tab character found here"
             <> (if tc == 1
                 then text ""
                 else text ", and in" <+> speakNOf (fromIntegral (tc - 1)) (text "further location"))
             <> text "."
    PsWarnTransitionalLayout reason
      -> mkSimpleDecorated $
            text "transitional layout will not be accepted in the future:"
            $$ text (case reason of
               TransLayout_Where -> "`where' clause at the same depth as implicit layout block"
               TransLayout_Pipe  -> "`|' at the same depth as implicit layout block"
            )
    PsWarnOperatorWhitespaceExtConflict sym
      -> let mk_prefix_msg operator_symbol extension_name syntax_meaning =
                  text "The prefix use of a" <+> quotes (text operator_symbol)
                    <+> text "would denote" <+> text syntax_meaning
               $$ nest 2 (text "were the" <+> text extension_name <+> text "extension enabled.")
               $$ text "Suggested fix: add whitespace after the"
                    <+> quotes (text operator_symbol) <> char '.'
         in mkSimpleDecorated $
         case sym of
           OperatorWhitespaceSymbol_PrefixPercent -> mk_prefix_msg "%" "LinearTypes" "a multiplicity annotation"
           OperatorWhitespaceSymbol_PrefixDollar -> mk_prefix_msg "$" "TemplateHaskell" "an untyped splice"
           OperatorWhitespaceSymbol_PrefixDollarDollar -> mk_prefix_msg "$$" "TemplateHaskell" "a typed splice"
    PsWarnOperatorWhitespace sym occ_type
      -> let mk_msg occ_type_str =
                  text "The" <+> text occ_type_str <+> text "use of a" <+> quotes (ftext sym)
                    <+> text "might be repurposed as special syntax"
               $$ nest 2 (text "by a future language extension.")
               $$ text "Suggested fix: add whitespace around it."
         in mkSimpleDecorated $
         case occ_type of
           OperatorWhitespaceOccurrence_Prefix -> mk_msg "prefix"
           OperatorWhitespaceOccurrence_Suffix -> mk_msg "suffix"
           OperatorWhitespaceOccurrence_TightInfix -> mk_msg "tight infix"
    PsWarnStarBinder
      -> mkSimpleDecorated $
            text "Found binding occurrence of" <+> quotes (text "*")
            <+> text "yet StarIsType is enabled."
         $$ text "NB. To use (or export) this operator in"
            <+> text "modules with StarIsType,"
         $$ text "    including the definition module, you must qualify it."
    PsWarnStarIsType
      -> mkSimpleDecorated $
             text "Using" <+> quotes (text "*")
             <+> text "(or its Unicode variant) to mean"
             <+> quotes (text "Data.Kind.Type")
          $$ text "relies on the StarIsType extension, which will become"
          $$ text "deprecated in the future."
          $$ text "Suggested fix: use" <+> quotes (text "Type")
           <+> text "from" <+> quotes (text "Data.Kind") <+> text "instead."
    PsWarnUnrecognisedPragma
      -> mkSimpleDecorated $ text "Unrecognised pragma"
    PsWarnImportPreQualified
      -> mkSimpleDecorated $
            text "Found" <+> quotes (text "qualified")
             <+> text "in prepositive position"
         $$ text "Suggested fix: place " <+> quotes (text "qualified")
             <+> text "after the module name instead."
         $$ text "To allow this, enable language extension 'ImportQualifiedPost'"

    PsErrLexer err kind
      -> mkSimpleDecorated $ hcat
           [ text $ case err of
              LexError               -> "lexical error"
              LexUnknownPragma       -> "unknown pragma"
              LexErrorInPragma       -> "lexical error in pragma"
              LexNumEscapeRange      -> "numeric escape sequence out of range"
              LexStringCharLit       -> "lexical error in string/character literal"
              LexStringCharLitEOF    -> "unexpected end-of-file in string/character literal"
              LexUnterminatedComment -> "unterminated `{-'"
              LexUnterminatedOptions -> "unterminated OPTIONS pragma"
              LexUnterminatedQQ      -> "unterminated quasiquotation"

           , text $ case kind of
              LexErrKind_EOF    -> " at end of input"
              LexErrKind_UTF8   -> " (UTF-8 decoding error)"
              LexErrKind_Char c -> " at character " ++ show c
           ]
    PsErrParse token _details
      | null token
      -> mkSimpleDecorated $ text "parse error (possibly incorrect indentation or mismatched brackets)"
      | otherwise
      -> mkSimpleDecorated $ text "parse error on input" <+> quotes (text token)
    PsErrCmmLexer
      -> mkSimpleDecorated $ text "Cmm lexical error"
    PsErrCmmParser cmm_err -> mkSimpleDecorated $ case cmm_err of
      CmmUnknownPrimitive name     -> text "unknown primitive" <+> ftext name
      CmmUnknownMacro fun          -> text "unknown macro" <+> ftext fun
      CmmUnknownCConv cconv        -> text "unknown calling convention:" <+> text cconv
      CmmUnrecognisedSafety safety -> text "unrecognised safety" <+> text safety
      CmmUnrecognisedHint hint     -> text "unrecognised hint:" <+> text hint

    PsErrTypeAppWithoutSpace v e
      -> mkSimpleDecorated $
           sep [ text "@-pattern in expression context:"
               , nest 4 (pprPrefixOcc v <> text "@" <> ppr e)
               ]
           $$ text "Type application syntax requires a space before '@'"
    PsErrLazyPatWithoutSpace e
      -> mkSimpleDecorated $
           sep [ text "Lazy pattern in expression context:"
               , nest 4 (text "~" <> ppr e)
               ]
           $$ text "Did you mean to add a space after the '~'?"
    PsErrBangPatWithoutSpace e
      -> mkSimpleDecorated $
           sep [ text "Bang pattern in expression context:"
               , nest 4 (text "!" <> ppr e)
               ]
           $$ text "Did you mean to add a space after the '!'?"
    PsErrInvalidInfixHole
      -> mkSimpleDecorated $ text "Invalid infix hole, expected an infix operator"
    PsErrExpectedHyphen
      -> mkSimpleDecorated $ text "Expected a hyphen"
    PsErrSpaceInSCC
      -> mkSimpleDecorated $ text "Spaces are not allowed in SCCs"
    PsErrEmptyDoubleQuotes th_on
      -> mkSimpleDecorated $ if th_on then vcat (msg ++ th_msg) else vcat msg
         where
            msg    = [ text "Parser error on `''`"
                     , text "Character literals may not be empty"
                     ]
            th_msg = [ text "Or perhaps you intended to use quotation syntax of TemplateHaskell,"
                     , text "but the type variable or constructor is missing"
                     ]

    PsErrLambdaCase
      -> mkSimpleDecorated $ text "Illegal lambda-case (use LambdaCase)"
    PsErrEmptyLambda
       -> mkSimpleDecorated $ text "A lambda requires at least one parameter"
    PsErrLinearFunction
      -> mkSimpleDecorated $ text "Enable LinearTypes to allow linear functions"
    PsErrOverloadedRecordUpdateNotEnabled
      -> mkSimpleDecorated $ text "OverloadedRecordUpdate needs to be enabled"
    PsErrMultiWayIf
      -> mkSimpleDecorated $ text "Multi-way if-expressions need MultiWayIf turned on"
    PsErrNumUnderscores reason
      -> mkSimpleDecorated $
           text $ case reason of
             NumUnderscore_Integral -> "Use NumericUnderscores to allow underscores in integer literals"
             NumUnderscore_Float    -> "Use NumericUnderscores to allow underscores in floating literals"
    PsErrIllegalBangPattern e
      -> mkSimpleDecorated $ text "Illegal bang-pattern (use BangPatterns):" $$ ppr e
    PsErrOverloadedRecordDotInvalid
      -> mkSimpleDecorated $
           text "Use of OverloadedRecordDot '.' not valid ('.' isn't allowed when constructing records or in record patterns)"
    PsErrIllegalPatSynExport
      -> mkSimpleDecorated $ text "Illegal export form (use PatternSynonyms to enable)"
    PsErrOverloadedRecordUpdateNoQualifiedFields
      -> mkSimpleDecorated $ text "Fields cannot be qualified when OverloadedRecordUpdate is enabled"
    PsErrExplicitForall is_unicode
      -> mkSimpleDecorated $ vcat
           [ text "Illegal symbol" <+> quotes (forallSym is_unicode) <+> text "in type"
           , text "Perhaps you intended to use RankNTypes or a similar language"
           , text "extension to enable explicit-forall syntax:" <+>
             forallSym is_unicode <+> text "<tvs>. <type>"
           ]
         where
          forallSym True  = text "∀"
          forallSym False = text "forall"
    PsErrIllegalQualifiedDo qdoDoc
      -> mkSimpleDecorated $ vcat
           [ text "Illegal qualified" <+> quotes qdoDoc <+> text "block"
           , text "Perhaps you intended to use QualifiedDo"
           ]
    PsErrQualifiedDoInCmd m
      -> mkSimpleDecorated $
           hang (text "Parse error in command:") 2 $
             text "Found a qualified" <+> ppr m <> text ".do block in a command, but"
             $$ text "qualified 'do' is not supported in commands."
    PsErrRecordSyntaxInPatSynDecl pat
      -> mkSimpleDecorated $
           text "record syntax not supported for pattern synonym declarations:"
           $$ ppr pat
    PsErrEmptyWhereInPatSynDecl patsyn_name
      -> mkSimpleDecorated $
           text "pattern synonym 'where' clause cannot be empty"
           $$ text "In the pattern synonym declaration for: "
              <+> ppr (patsyn_name)
    PsErrInvalidWhereBindInPatSynDecl patsyn_name decl
      -> mkSimpleDecorated $
           text "pattern synonym 'where' clause must bind the pattern synonym's name"
           <+> quotes (ppr patsyn_name) $$ ppr decl
    PsErrNoSingleWhereBindInPatSynDecl _patsyn_name decl
      -> mkSimpleDecorated $
           text "pattern synonym 'where' clause must contain a single binding:"
           $$ ppr decl
    PsErrDeclSpliceNotAtTopLevel d
      -> mkSimpleDecorated $
           hang (text "Declaration splices are allowed only"
                 <+> text "at the top level:")
             2 (ppr d)
    PsErrMultipleNamesInStandaloneKindSignature vs
      -> mkSimpleDecorated $
           vcat [ hang (text "Standalone kind signatures do not support multiple names at the moment:")
                  2 (pprWithCommas ppr vs)
                , text "See https://gitlab.haskell.org/ghc/ghc/issues/16754 for details."
                ]
    PsErrIllegalExplicitNamespace
      -> mkSimpleDecorated $
           text "Illegal keyword 'type' (use ExplicitNamespaces to enable)"

    PsErrUnallowedPragma prag
      -> mkSimpleDecorated $
           hang (text "A pragma is not allowed in this position:") 2
                (ppr prag)
    PsErrImportPostQualified
      -> mkSimpleDecorated $
           text "Found" <+> quotes (text "qualified")
             <+> text "in postpositive position. "
           $$ text "To allow this, enable language extension 'ImportQualifiedPost'"
    PsErrImportQualifiedTwice
      -> mkSimpleDecorated $ text "Multiple occurrences of 'qualified'"
    PsErrIllegalImportBundleForm
      -> mkSimpleDecorated $
           text "Illegal import form, this syntax can only be used to bundle"
           $+$ text "pattern synonyms with types in module exports."
    PsErrInvalidRuleActivationMarker
      -> mkSimpleDecorated $ text "Invalid rule activation marker"

    PsErrMissingBlock
      -> mkSimpleDecorated $ text "Missing block"
    PsErrUnsupportedBoxedSumExpr s
      -> mkSimpleDecorated $
           hang (text "Boxed sums not supported:") 2
                (pprSumOrTuple Boxed s)
    PsErrUnsupportedBoxedSumPat s
      -> mkSimpleDecorated $
           hang (text "Boxed sums not supported:") 2
                (pprSumOrTuple Boxed s)
    PsErrUnexpectedQualifiedConstructor v
      -> mkSimpleDecorated $
           hang (text "Expected an unqualified type constructor:") 2
                (ppr v)
    PsErrTupleSectionInPat
      -> mkSimpleDecorated $ text "Tuple section in pattern context"
    PsErrOpFewArgs (StarIsType star_is_type) op
      -> mkSimpleDecorated $
           text "Operator applied to too few arguments:" <+> ppr op
           $$ starInfo star_is_type op
    PsErrVarForTyCon name
      -> mkSimpleDecorated $
           text "Expecting a type constructor but found a variable,"
             <+> quotes (ppr name) <> text "."
           $$ if isSymOcc $ rdrNameOcc name
              then text "If" <+> quotes (ppr name) <+> text "is a type constructor"
                    <+> text "then enable ExplicitNamespaces and use the 'type' keyword."
              else empty
    PsErrMalformedEntityString
      -> mkSimpleDecorated $ text "Malformed entity string"
    PsErrDotsInRecordUpdate
      -> mkSimpleDecorated $ text "You cannot use `..' in a record update"
    PsErrInvalidDataCon t
      -> mkSimpleDecorated $
           hang (text "Cannot parse data constructor in a data/newtype declaration:") 2
                (ppr t)
    PsErrInvalidInfixDataCon lhs tc rhs
      -> mkSimpleDecorated $
           hang (text "Cannot parse an infix data constructor in a data/newtype declaration:") 2
                (ppr lhs <+> ppr tc <+> ppr rhs)
    PsErrUnpackDataCon
      -> mkSimpleDecorated $ text "{-# UNPACK #-} cannot be applied to a data constructor."
    PsErrUnexpectedKindAppInDataCon lhs ki
      -> mkSimpleDecorated $
           hang (text "Unexpected kind application in a data/newtype declaration:") 2
                (ppr lhs <+> text "@" <> ppr ki)
    PsErrInvalidRecordCon p
      -> mkSimpleDecorated $ text "Not a record constructor:" <+> ppr p
    PsErrIllegalUnboxedStringInPat lit
      -> mkSimpleDecorated $ text "Illegal unboxed string literal in pattern:" $$ ppr lit
    PsErrDoNotationInPat
      -> mkSimpleDecorated $ text "do-notation in pattern"
    PsErrIfThenElseInPat
      -> mkSimpleDecorated $ text "(if ... then ... else ...)-syntax in pattern"
    PsErrLambdaCaseInPat
      -> mkSimpleDecorated $ text "(\\case ...)-syntax in pattern"
    PsErrCaseInPat
      -> mkSimpleDecorated $ text "(case ... of ...)-syntax in pattern"
    PsErrLetInPat
      -> mkSimpleDecorated $ text "(let ... in ...)-syntax in pattern"
    PsErrLambdaInPat
      -> mkSimpleDecorated $
           text "Lambda-syntax in pattern."
           $$ text "Pattern matching on functions is not possible."
    PsErrArrowExprInPat e
      -> mkSimpleDecorated $ text "Expression syntax in pattern:" <+> ppr e
    PsErrArrowCmdInPat c
      -> mkSimpleDecorated $ text "Command syntax in pattern:" <+> ppr c
    PsErrArrowCmdInExpr c
      -> mkSimpleDecorated $
           vcat
           [ text "Arrow command found where an expression was expected:"
           , nest 2 (ppr c)
           ]
    PsErrViewPatInExpr a b
      -> mkSimpleDecorated $
           sep [ text "View pattern in expression context:"
               , nest 4 (ppr a <+> text "->" <+> ppr b)
               ]
    PsErrLambdaCmdInFunAppCmd a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "lambda command") a
    PsErrCaseCmdInFunAppCmd a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "case command") a
    PsErrIfCmdInFunAppCmd a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "if command") a
    PsErrLetCmdInFunAppCmd a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "let command") a
    PsErrDoCmdInFunAppCmd a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "do command") a
    PsErrDoInFunAppExpr m a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (prependQualified m (text "do block")) a
    PsErrMDoInFunAppExpr m a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (prependQualified m (text "mdo block")) a
    PsErrLambdaInFunAppExpr a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "lambda expression") a
    PsErrCaseInFunAppExpr a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "case expression") a
    PsErrLambdaCaseInFunAppExpr a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "lambda-case expression") a
    PsErrLetInFunAppExpr a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "let expression") a
    PsErrIfInFunAppExpr a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "if expression") a
    PsErrProcInFunAppExpr a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "proc expression") a
    PsErrMalformedTyOrClDecl ty
      -> mkSimpleDecorated $
           text "Malformed head of type or class declaration:" <+> ppr ty
    PsErrIllegalWhereInDataDecl
      -> mkSimpleDecorated $
           vcat
              [ text "Illegal keyword 'where' in data declaration"
              , text "Perhaps you intended to use GADTs or a similar language"
              , text "extension to enable syntax: data T where"
              ]
    PsErrIllegalDataTypeContext c
      -> mkSimpleDecorated $
           text "Illegal datatype context (use DatatypeContexts):"
             <+> pprLHsContext (Just c)
    PsErrPrimStringInvalidChar
      -> mkSimpleDecorated $ text "primitive string literal must contain only characters <= \'\\xFF\'"
    PsErrSuffixAT
      -> mkSimpleDecorated $
           text "Suffix occurrence of @. For an as-pattern, remove the leading whitespace."
    PsErrPrecedenceOutOfRange i
      -> mkSimpleDecorated $ text "Precedence out of range: " <> int i
    PsErrSemiColonsInCondExpr c st t se e
      -> mkSimpleDecorated $
           text "Unexpected semi-colons in conditional:"
           $$ nest 4 expr
           $$ text "Perhaps you meant to use DoAndIfThenElse?"
         where
            pprOptSemi True  = semi
            pprOptSemi False = empty
            expr = text "if"   <+> ppr c <> pprOptSemi st <+>
                   text "then" <+> ppr t <> pprOptSemi se <+>
                   text "else" <+> ppr e
    PsErrSemiColonsInCondCmd c st t se e
      -> mkSimpleDecorated $
           text "Unexpected semi-colons in conditional:"
           $$ nest 4 expr
           $$ text "Perhaps you meant to use DoAndIfThenElse?"
         where
            pprOptSemi True  = semi
            pprOptSemi False = empty
            expr = text "if"   <+> ppr c <> pprOptSemi st <+>
                   text "then" <+> ppr t <> pprOptSemi se <+>
                   text "else" <+> ppr e
    PsErrAtInPatPos
      -> mkSimpleDecorated $
           text "Found a binding for the"
           <+> quotes (text "@")
           <+> text "operator in a pattern position."
           $$ perhapsAsPat
    PsErrParseErrorOnInput occ
      -> mkSimpleDecorated $ text "parse error on input" <+> ftext (occNameFS occ)
    PsErrMalformedDecl what for
      -> mkSimpleDecorated $
           text "Malformed" <+> what
           <+> text "declaration for" <+> quotes (ppr for)
    PsErrUnexpectedTypeAppInDecl ki what for
      -> mkSimpleDecorated $
           vcat [ text "Unexpected type application"
                  <+> text "@" <> ppr ki
                , text "In the" <+> what
                  <+> text "declaration for"
                  <+> quotes (ppr for)
                ]
    PsErrNotADataCon name
      -> mkSimpleDecorated $ text "Not a data constructor:" <+> quotes (ppr name)
    PsErrInferredTypeVarNotAllowed
      -> mkSimpleDecorated $ text "Inferred type variables are not allowed here"
    PsErrIllegalTraditionalRecordSyntax s
      -> mkSimpleDecorated $
           text "Illegal record syntax (use TraditionalRecordSyntax):" <+> s
    PsErrParseErrorInCmd s
      -> mkSimpleDecorated $ hang (text "Parse error in command:") 2 s
    PsErrInPat s details
      -> let msg  = parse_error_in_pat
             body = case details of
                 PEIP_NegApp -> text "-" <> ppr s
                 PEIP_TypeArgs peipd_tyargs
                   | not (null peipd_tyargs) -> ppr s <+> vcat [
                               hsep [text "@" <> ppr t | t <- peipd_tyargs]
                             , text "Type applications in patterns are only allowed on data constructors."
                             ]
                   | otherwise -> ppr s
                 PEIP_OtherPatDetails (ParseContext (Just fun) _)
                  -> ppr s <+> text "In a function binding for the"
                                     <+> quotes (ppr fun)
                                     <+> text "operator."
                                  $$ if opIsAt fun
                                        then perhapsAsPat
                                        else empty
                 _  -> ppr s
         in mkSimpleDecorated $ msg <+> body
    PsErrParseRightOpSectionInPat infixOcc s
      -> mkSimpleDecorated $ parse_error_in_pat <+> pprInfixOcc infixOcc <> ppr s
    PsErrIllegalRoleName role nearby
      -> mkSimpleDecorated $
           text "Illegal role name" <+> quotes (ppr role)
           $$ case nearby of
               []  -> empty
               [r] -> text "Perhaps you meant" <+> quotes (ppr r)
               -- will this last case ever happen??
               _   -> hang (text "Perhaps you meant one of these:")
                           2 (pprWithCommas (quotes . ppr) nearby)
    PsErrInvalidTypeSignature lhs
      -> mkSimpleDecorated $
           text "Invalid type signature:"
           <+> ppr lhs
           <+> text ":: ..."
           $$ text hint
         where
         hint | foreign_RDR `looks_like` lhs
              = "Perhaps you meant to use ForeignFunctionInterface?"
              | default_RDR `looks_like` lhs
              = "Perhaps you meant to use DefaultSignatures?"
              | pattern_RDR `looks_like` lhs
              = "Perhaps you meant to use PatternSynonyms?"
              | otherwise
              = "Should be of form <variable> :: <type>"

         -- A common error is to forget the ForeignFunctionInterface flag
         -- so check for that, and suggest.  cf #3805
         -- Sadly 'foreign import' still barfs 'parse error' because
         --  'import' is a keyword
         -- looks_like :: RdrName -> LHsExpr GhcPsErr -> Bool -- AZ
         looks_like s (L _ (HsVar _ (L _ v))) = v == s
         looks_like s (L _ (HsApp _ lhs _))   = looks_like s lhs
         looks_like _ _                       = False

         foreign_RDR = mkUnqual varName (fsLit "foreign")
         default_RDR = mkUnqual varName (fsLit "default")
         pattern_RDR = mkUnqual varName (fsLit "pattern")
    PsErrUnexpectedTypeInDecl t what tc tparms equals_or_where
       -> mkSimpleDecorated $
            vcat [ text "Unexpected type" <+> quotes (ppr t)
                 , text "In the" <+> what
                   <+> text "declaration for" <+> quotes tc'
                 , vcat[ (text "A" <+> what
                          <+> text "declaration should have form")
                 , nest 2
                   (what
                    <+> tc'
                    <+> hsep (map text (takeList tparms allNameStrings))
                    <+> equals_or_where) ] ]
           where
             -- Avoid printing a constraint tuple in the error message. Print
             -- a plain old tuple instead (since that's what the user probably
             -- wrote). See #14907
             tc' = ppr $ filterCTuple tc
    PsErrInvalidPackageName pkg
      -> mkSimpleDecorated $ vcat
            [ text "Parse error" <> colon <+> quotes (ftext pkg)
            , text "Version number or non-alphanumeric" <+>
              text "character in package name"
            ]

  diagnosticReason  = \case
    PsUnknownMessage m                            -> diagnosticReason m
    PsWarnTab{}                                   -> WarningWithFlag Opt_WarnTabs
    PsWarnTransitionalLayout{}                    -> WarningWithFlag Opt_WarnAlternativeLayoutRuleTransitional
    PsWarnOperatorWhitespaceExtConflict{}         -> WarningWithFlag Opt_WarnOperatorWhitespaceExtConflict
    PsWarnOperatorWhitespace{}                    -> WarningWithFlag Opt_WarnOperatorWhitespace
    PsWarnHaddockInvalidPos                       -> WarningWithFlag Opt_WarnInvalidHaddock
    PsWarnHaddockIgnoreMulti                      -> WarningWithFlag Opt_WarnInvalidHaddock
    PsWarnStarBinder                              -> WarningWithFlag Opt_WarnStarBinder
    PsWarnStarIsType                              -> WarningWithFlag Opt_WarnStarIsType
    PsWarnUnrecognisedPragma                      -> WarningWithFlag Opt_WarnUnrecognisedPragmas
    PsWarnImportPreQualified                      -> WarningWithFlag Opt_WarnPrepositiveQualifiedModule
    PsErrLexer{}                                  -> ErrorWithoutFlag
    PsErrCmmLexer                                 -> ErrorWithoutFlag
    PsErrCmmParser{}                              -> ErrorWithoutFlag
    PsErrParse{}                                  -> ErrorWithoutFlag
    PsErrTypeAppWithoutSpace{}                    -> ErrorWithoutFlag
    PsErrLazyPatWithoutSpace{}                    -> ErrorWithoutFlag
    PsErrBangPatWithoutSpace{}                    -> ErrorWithoutFlag
    PsErrInvalidInfixHole                         -> ErrorWithoutFlag
    PsErrExpectedHyphen                           -> ErrorWithoutFlag
    PsErrSpaceInSCC                               -> ErrorWithoutFlag
    PsErrEmptyDoubleQuotes{}                      -> ErrorWithoutFlag
    PsErrLambdaCase{}                             -> ErrorWithoutFlag
    PsErrEmptyLambda{}                            -> ErrorWithoutFlag
    PsErrLinearFunction{}                         -> ErrorWithoutFlag
    PsErrMultiWayIf{}                             -> ErrorWithoutFlag
    PsErrOverloadedRecordUpdateNotEnabled{}       -> ErrorWithoutFlag
    PsErrNumUnderscores{}                         -> ErrorWithoutFlag
    PsErrIllegalBangPattern{}                     -> ErrorWithoutFlag
    PsErrOverloadedRecordDotInvalid{}             -> ErrorWithoutFlag
    PsErrIllegalPatSynExport                      -> ErrorWithoutFlag
    PsErrOverloadedRecordUpdateNoQualifiedFields  -> ErrorWithoutFlag
    PsErrExplicitForall{}                         -> ErrorWithoutFlag
    PsErrIllegalQualifiedDo{}                     -> ErrorWithoutFlag
    PsErrQualifiedDoInCmd{}                       -> ErrorWithoutFlag
    PsErrRecordSyntaxInPatSynDecl{}               -> ErrorWithoutFlag
    PsErrEmptyWhereInPatSynDecl{}                 -> ErrorWithoutFlag
    PsErrInvalidWhereBindInPatSynDecl{}           -> ErrorWithoutFlag
    PsErrNoSingleWhereBindInPatSynDecl{}          -> ErrorWithoutFlag
    PsErrDeclSpliceNotAtTopLevel{}                -> ErrorWithoutFlag
    PsErrMultipleNamesInStandaloneKindSignature{} -> ErrorWithoutFlag
    PsErrIllegalExplicitNamespace                 -> ErrorWithoutFlag
    PsErrUnallowedPragma{}                        -> ErrorWithoutFlag
    PsErrImportPostQualified                      -> ErrorWithoutFlag
    PsErrImportQualifiedTwice                     -> ErrorWithoutFlag
    PsErrIllegalImportBundleForm                  -> ErrorWithoutFlag
    PsErrInvalidRuleActivationMarker              -> ErrorWithoutFlag
    PsErrMissingBlock                             -> ErrorWithoutFlag
    PsErrUnsupportedBoxedSumExpr{}                -> ErrorWithoutFlag
    PsErrUnsupportedBoxedSumPat{}                 -> ErrorWithoutFlag
    PsErrUnexpectedQualifiedConstructor{}         -> ErrorWithoutFlag
    PsErrTupleSectionInPat{}                      -> ErrorWithoutFlag
    PsErrOpFewArgs{}                              -> ErrorWithoutFlag
    PsErrVarForTyCon{}                            -> ErrorWithoutFlag
    PsErrMalformedEntityString                    -> ErrorWithoutFlag
    PsErrDotsInRecordUpdate                       -> ErrorWithoutFlag
    PsErrInvalidDataCon{}                         -> ErrorWithoutFlag
    PsErrInvalidInfixDataCon{}                    -> ErrorWithoutFlag
    PsErrUnpackDataCon                            -> ErrorWithoutFlag
    PsErrUnexpectedKindAppInDataCon{}             -> ErrorWithoutFlag
    PsErrInvalidRecordCon{}                       -> ErrorWithoutFlag
    PsErrIllegalUnboxedStringInPat{}              -> ErrorWithoutFlag
    PsErrDoNotationInPat{}                        -> ErrorWithoutFlag
    PsErrIfThenElseInPat                          -> ErrorWithoutFlag
    PsErrLambdaCaseInPat                          -> ErrorWithoutFlag
    PsErrCaseInPat                                -> ErrorWithoutFlag
    PsErrLetInPat                                 -> ErrorWithoutFlag
    PsErrLambdaInPat                              -> ErrorWithoutFlag
    PsErrArrowExprInPat{}                         -> ErrorWithoutFlag
    PsErrArrowCmdInPat{}                          -> ErrorWithoutFlag
    PsErrArrowCmdInExpr{}                         -> ErrorWithoutFlag
    PsErrViewPatInExpr{}                          -> ErrorWithoutFlag
    PsErrLambdaCmdInFunAppCmd{}                   -> ErrorWithoutFlag
    PsErrCaseCmdInFunAppCmd{}                     -> ErrorWithoutFlag
    PsErrIfCmdInFunAppCmd{}                       -> ErrorWithoutFlag
    PsErrLetCmdInFunAppCmd{}                      -> ErrorWithoutFlag
    PsErrDoCmdInFunAppCmd{}                       -> ErrorWithoutFlag
    PsErrDoInFunAppExpr{}                         -> ErrorWithoutFlag
    PsErrMDoInFunAppExpr{}                        -> ErrorWithoutFlag
    PsErrLambdaInFunAppExpr{}                     -> ErrorWithoutFlag
    PsErrCaseInFunAppExpr{}                       -> ErrorWithoutFlag
    PsErrLambdaCaseInFunAppExpr{}                 -> ErrorWithoutFlag
    PsErrLetInFunAppExpr{}                        -> ErrorWithoutFlag
    PsErrIfInFunAppExpr{}                         -> ErrorWithoutFlag
    PsErrProcInFunAppExpr{}                       -> ErrorWithoutFlag
    PsErrMalformedTyOrClDecl{}                    -> ErrorWithoutFlag
    PsErrIllegalWhereInDataDecl                   -> ErrorWithoutFlag
    PsErrIllegalDataTypeContext{}                 -> ErrorWithoutFlag
    PsErrPrimStringInvalidChar                    -> ErrorWithoutFlag
    PsErrSuffixAT                                 -> ErrorWithoutFlag
    PsErrPrecedenceOutOfRange{}                   -> ErrorWithoutFlag
    PsErrSemiColonsInCondExpr{}                   -> ErrorWithoutFlag
    PsErrSemiColonsInCondCmd{}                    -> ErrorWithoutFlag
    PsErrAtInPatPos                               -> ErrorWithoutFlag
    PsErrParseErrorOnInput{}                      -> ErrorWithoutFlag
    PsErrMalformedDecl{}                          -> ErrorWithoutFlag
    PsErrUnexpectedTypeAppInDecl{}                -> ErrorWithoutFlag
    PsErrNotADataCon{}                            -> ErrorWithoutFlag
    PsErrInferredTypeVarNotAllowed                -> ErrorWithoutFlag
    PsErrIllegalTraditionalRecordSyntax{}         -> ErrorWithoutFlag
    PsErrParseErrorInCmd{}                        -> ErrorWithoutFlag
    PsErrInPat{}                                  -> ErrorWithoutFlag
    PsErrIllegalRoleName{}                        -> ErrorWithoutFlag
    PsErrInvalidTypeSignature{}                   -> ErrorWithoutFlag
    PsErrUnexpectedTypeInDecl{}                   -> ErrorWithoutFlag
    PsErrInvalidPackageName{}                     -> ErrorWithoutFlag
    PsErrParseRightOpSectionInPat{}               -> ErrorWithoutFlag

  diagnosticHints  = \case
    PsUnknownMessage m                            -> diagnosticHints m
    PsWarnTab{}                                   -> [SuggestUseSpaces]
    PsWarnTransitionalLayout{}                    -> noHints
    PsWarnOperatorWhitespaceExtConflict{}         -> noHints
    PsWarnOperatorWhitespace{}                    -> noHints
    PsWarnHaddockInvalidPos                       -> noHints
    PsWarnHaddockIgnoreMulti                      -> noHints
    PsWarnStarBinder                              -> noHints
    PsWarnStarIsType                              -> noHints
    PsWarnUnrecognisedPragma                      -> noHints
    PsWarnImportPreQualified                      -> noHints
    PsErrLexer{}                                  -> noHints
    PsErrCmmLexer                                 -> noHints
    PsErrCmmParser{}                              -> noHints
    PsErrParse token PsErrParseDetails{..}        -> case token of
      ""                         -> []
      "$"  | not ped_th_enabled  -> [SuggestExtension LangExt.TemplateHaskell]   -- #7396
      "<-" | ped_mdo_in_last_100 -> [SuggestExtension LangExt.RecursiveDo]
           | otherwise           -> [SuggestMissingDo]
      "="  | ped_do_in_last_100  -> [SuggestLetInDo]                             -- #15849
      _    | not ped_pat_syn_enabled
           , ped_pattern_parsed  -> [SuggestExtension LangExt.PatternSynonyms]   -- #12429
           | otherwise           -> []
    PsErrTypeAppWithoutSpace{}                    -> noHints
    PsErrLazyPatWithoutSpace{}                    -> noHints
    PsErrBangPatWithoutSpace{}                    -> noHints
    PsErrInvalidInfixHole                         -> noHints
    PsErrExpectedHyphen                           -> noHints
    PsErrSpaceInSCC                               -> noHints
    PsErrEmptyDoubleQuotes{}                      -> noHints
    PsErrLambdaCase{}                             -> noHints
    PsErrEmptyLambda{}                            -> noHints
    PsErrLinearFunction{}                         -> noHints
    PsErrMultiWayIf{}                             -> noHints
    PsErrOverloadedRecordUpdateNotEnabled{}       -> noHints
    PsErrNumUnderscores{}                         -> noHints
    PsErrIllegalBangPattern{}                     -> noHints
    PsErrOverloadedRecordDotInvalid{}             -> noHints
    PsErrIllegalPatSynExport                      -> noHints
    PsErrOverloadedRecordUpdateNoQualifiedFields  -> noHints
    PsErrExplicitForall{}                         -> noHints
    PsErrIllegalQualifiedDo{}                     -> noHints
    PsErrQualifiedDoInCmd{}                       -> noHints
    PsErrRecordSyntaxInPatSynDecl{}               -> noHints
    PsErrEmptyWhereInPatSynDecl{}                 -> noHints
    PsErrInvalidWhereBindInPatSynDecl{}           -> noHints
    PsErrNoSingleWhereBindInPatSynDecl{}          -> noHints
    PsErrDeclSpliceNotAtTopLevel{}                -> noHints
    PsErrMultipleNamesInStandaloneKindSignature{} -> noHints
    PsErrIllegalExplicitNamespace                 -> noHints
    PsErrUnallowedPragma{}                        -> noHints
    PsErrImportPostQualified                      -> noHints
    PsErrImportQualifiedTwice                     -> noHints
    PsErrIllegalImportBundleForm                  -> noHints
    PsErrInvalidRuleActivationMarker              -> noHints
    PsErrMissingBlock                             -> noHints
    PsErrUnsupportedBoxedSumExpr{}                -> noHints
    PsErrUnsupportedBoxedSumPat{}                 -> noHints
    PsErrUnexpectedQualifiedConstructor{}         -> noHints
    PsErrTupleSectionInPat{}                      -> noHints
    PsErrOpFewArgs{}                              -> noHints
    PsErrVarForTyCon{}                            -> noHints
    PsErrMalformedEntityString                    -> noHints
    PsErrDotsInRecordUpdate                       -> noHints
    PsErrInvalidDataCon{}                         -> noHints
    PsErrInvalidInfixDataCon{}                    -> noHints
    PsErrUnpackDataCon                            -> noHints
    PsErrUnexpectedKindAppInDataCon{}             -> noHints
    PsErrInvalidRecordCon{}                       -> noHints
    PsErrIllegalUnboxedStringInPat{}              -> noHints
    PsErrDoNotationInPat{}                        -> noHints
    PsErrIfThenElseInPat                          -> noHints
    PsErrLambdaCaseInPat                          -> noHints
    PsErrCaseInPat                                -> noHints
    PsErrLetInPat                                 -> noHints
    PsErrLambdaInPat                              -> noHints
    PsErrArrowExprInPat{}                         -> noHints
    PsErrArrowCmdInPat{}                          -> noHints
    PsErrArrowCmdInExpr{}                         -> noHints
    PsErrViewPatInExpr{}                          -> noHints
    PsErrLambdaCmdInFunAppCmd{}                   -> suggestParensAndBlockArgs
    PsErrCaseCmdInFunAppCmd{}                     -> suggestParensAndBlockArgs
    PsErrIfCmdInFunAppCmd{}                       -> suggestParensAndBlockArgs
    PsErrLetCmdInFunAppCmd{}                      -> suggestParensAndBlockArgs
    PsErrDoCmdInFunAppCmd{}                       -> suggestParensAndBlockArgs
    PsErrDoInFunAppExpr{}                         -> suggestParensAndBlockArgs
    PsErrMDoInFunAppExpr{}                        -> suggestParensAndBlockArgs
    PsErrLambdaInFunAppExpr{}                     -> suggestParensAndBlockArgs
    PsErrCaseInFunAppExpr{}                       -> suggestParensAndBlockArgs
    PsErrLambdaCaseInFunAppExpr{}                 -> suggestParensAndBlockArgs
    PsErrLetInFunAppExpr{}                        -> suggestParensAndBlockArgs
    PsErrIfInFunAppExpr{}                         -> suggestParensAndBlockArgs
    PsErrProcInFunAppExpr{}                       -> suggestParensAndBlockArgs
    PsErrMalformedTyOrClDecl{}                    -> noHints
    PsErrIllegalWhereInDataDecl                   -> noHints
    PsErrIllegalDataTypeContext{}                 -> noHints
    PsErrPrimStringInvalidChar                    -> noHints
    PsErrSuffixAT                                 -> noHints
    PsErrPrecedenceOutOfRange{}                   -> noHints
    PsErrSemiColonsInCondExpr{}                   -> noHints
    PsErrSemiColonsInCondCmd{}                    -> noHints
    PsErrAtInPatPos                               -> noHints
    PsErrParseErrorOnInput{}                      -> noHints
    PsErrMalformedDecl{}                          -> noHints
    PsErrUnexpectedTypeAppInDecl{}                -> noHints
    PsErrNotADataCon{}                            -> noHints
    PsErrInferredTypeVarNotAllowed                -> noHints
    PsErrIllegalTraditionalRecordSyntax{}         -> noHints
    PsErrParseErrorInCmd{}                        -> noHints
    PsErrInPat _ details                          -> case details of
      PEIP_RecPattern args YesPatIsRecursive ctx
       | length args /= 0 -> catMaybes [sug_recdo, sug_missingdo ctx]
       | otherwise        -> catMaybes [sug_missingdo ctx]
      PEIP_OtherPatDetails ctx -> catMaybes [sug_missingdo ctx]
      _                        -> []
      where
        sug_recdo                                           = Just (SuggestExtension LangExt.RecursiveDo)
        sug_missingdo (ParseContext _ YesIncompleteDoBlock) = Just SuggestMissingDo
        sug_missingdo _                                     = Nothing
    PsErrParseRightOpSectionInPat{}               -> noHints
    PsErrIllegalRoleName{}                        -> noHints
    PsErrInvalidTypeSignature{}                   -> noHints
    PsErrUnexpectedTypeInDecl{}                   -> noHints
    PsErrInvalidPackageName{}                     -> noHints

suggestParensAndBlockArgs :: [GhcHint]
suggestParensAndBlockArgs =
  [SuggestParentheses, SuggestExtension LangExt.BlockArguments]

pp_unexpected_fun_app :: Outputable a => SDoc -> a -> SDoc
pp_unexpected_fun_app e a =
   text "Unexpected " <> e <> text " in function application:"
    $$ nest 4 (ppr a)

parse_error_in_pat :: SDoc
parse_error_in_pat = text "Parse error in pattern:"

perhapsAsPat :: SDoc
perhapsAsPat = text "Perhaps you meant an as-pattern, which must not be surrounded by whitespace"
