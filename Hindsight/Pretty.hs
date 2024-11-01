module Hindsight.Pretty where
import Hindsight.Syntax
import Hindsight.TypeChecker

import MinHS.Pretty hiding (ansipp')
import MinHS.Syntax(Op(..),TyCon(..))

import Prettyprinter as PP
import Prettyprinter.Render.Terminal

instance {-# OVERLAPPING #-} ANSIPretty CBind where
  ansipp (CBind n ty ps exp) = pretty n <+> symbol "::" <+> ansipp ty
                                       <+> params (symbol "=" <+> ansipp exp)
      where params = if null ps then id else (hsep (map pretty ps) <+>)
  ansippList = vcat . map (<> semi) . map ansipp

instance Pretty CBind where
  pretty = unAnnotate . ansipp

instance {-# OVERLAPPING #-} ANSIPretty VBind where
  ansipp (VBind n ty exp) = pretty n <+> symbol "::" <+> ansipp ty
                                     <+> symbol "=" <+> ansipp exp

instance {-# OVERLAPPING #-} ANSIPretty CType where
  ansipp = ansippCType
    where
      ansippCType (a `Arrow` b) = ansipp a <+> symbol "->" <+> ansippCType b
      ansippCType (F t) = typecon "F" <+> ansippVType'' t

instance {-# OVERLAPPING #-} ANSIPretty VType where
  ansipp = ansippVType

ansippVType (TypeApp (TypeCon List) b) = blue (brackets (ansippVType b))
ansippVType (TypeApp a b) = ansippVType a <+> ansippVType'' b
ansippVType (TypeCon Unit) = typecon "()"
ansippVType (TypeCon x)    = typecon $ show x
ansippVType (U x)    = typecon "U" <+> parens(ansipp x)
ansippVType' t = ansippVType t
ansippVType'' t@(TypeApp (TypeCon List) _) = ansippVType' t
ansippVType'' t@(TypeApp _ _) = parens (ansippVType' t)
ansippVType'' t@(U _) = parens (ansippVType' t)
ansippVType'' t = ansippVType' t

instance {-# OVERLAPPING #-} ANSIPretty CExp where
  ansipp (Produce v) = keyword "produce" <+> ansipp'' v
  ansipp (Force v) = keyword "force" <+> ansipp'' v
  ansipp (Reduce id e1 e2) =
    align(keyword "reduce" <+>
          PP.vsep [ansipp e1, keyword "to" <+> pretty id <+> keyword "in" <+> ansipp e2])
  ansipp (Let bs e)  = align (PP.vsep [keyword "let" <+> align (encloseSep mempty semi mempty $ map ansipp bs)
                                      , keyword "in" <+> ansipp e])
  ansipp (App (Prim Neg) e2) = parens (pretty "-" <+> ansipp'' e2)
  ansipp (Prim Head) = pretty "head"
  ansipp (Prim Tail) = pretty "tail"
  ansipp (Prim Null) = pretty "null"  
  ansipp (Prim o) = parens (ansipp o)
  ansipp (App e1 e2) = ansipp e1 <+> ansipp'' e2
  ansipp (If c t e) =  keyword "if"
                   <+> align (PP.vsep [ansipp c
                                      , keyword "then" <+> ansipp t
                                      ,keyword "else" <+> ansipp e])
  ansipp (Recfun b)  = parens (keyword "recfun" <+> ansipp b)

instance {-# OVERLAPPING #-} ANSIPretty VExp where
  ansipp (Var i) = pretty i
  ansipp (Con i) = datacon i
  ansipp (Num i) = numeric i
  ansipp (Thunk c) = keyword "thunk" <+> ansipp' c

ansipp' t@(App _ _) = parens (ansipp t)
ansipp' t@(Force _) = parens (ansipp t)
ansipp' t@(Produce _) = parens (ansipp t)
ansipp' t           = ansipp t

ansipp'' t@(Thunk _) = parens (ansipp t)
ansipp'' t           = ansipp t

instance {-# OVERLAPPING #-} ANSIPretty TypeError where
   ansipp (TypeMismatch t1 t2 e) = PP.vsep [ err "Type mismatch:"
                                           , indent 3 (ansipp t1)
                                           , err "is not"
                                           , indent 3 (ansipp t2)
                                           , err "in expression"
                                           , indent 3 (ansipp e)]
   ansipp (Unreducible t e) =  PP.vsep [ err "Cannot reduce non-F type"
                                       , indent 3 (ansipp t)
                                       , err "in expression"
                                       , indent 3 (ansipp e)]
   ansipp (VTypeMismatch t1 t2 e) = PP.vsep [ err "Type mismatch:"
                                            , indent 3 (ansipp t1)
                                            , err "is not"
                                            , indent 3 (ansipp t2)
                                            , err "in expression"
                                            , indent 3 (ansipp e)]
   ansipp (TypeShouldBeFunction ty b) =
     PP.vsep [ err "Parameter list suggests this atomic type"
             , indent 3 (ansipp ty)
             , err "to be a function, in binding:"
             , indent 3 (ansipp b)]
   ansipp (ForceNonThunk ty e) = PP.vsep [ err "Cannot force non-thunk type"
                                         , indent 3 (ansipp ty)
                                         , err "in expression"
                                         , indent 3 (ansipp e)]
   ansipp (FunctionTypeExpected e t) =
     PP.vsep [err "Function application must be performed on a function, but this:"
             , indent 3 (ansipp e)
             , err "is of type" <+> ansipp t]
   ansipp (NoSuchVariable x) =  err "Variable"
                            <+> pretty x
                            <+> err "not in scope."
   ansipp (NoSuchConstructor x) =  err "Constructor"
                               <+> pretty x
                               <+> err "not in scope."
   ansipp (TypeConstructorSaturated t k) =  err "Expected"
                                        <+> ansipp t
                                        <+> err "to be a type constructor, but it is an atomic type."
   ansipp (KindMismatch k1 k2 t) =  err "Type term"
                                <+> ansipp t
                                <+> err "is not valid."
