{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
module MinHS.Pretty where
import MinHS.Syntax
import MinHS.TypeChecker

import Prettyprinter as PP
import Prettyprinter.Render.Terminal

primop :: String -> Doc AnsiStyle
primop = annotate (colorDull Yellow) . pretty

blue = annotate (color Blue)
keyword = annotate bold . pretty
datacon = annotate (colorDull Green) . pretty
typecon = annotate (color Blue) . pretty
numeric = annotate (colorDull Cyan) . pretty
symbol = annotate (color Magenta) . pretty
err = annotate (color Red) . pretty

-- Helper typeclass to for specialising to an AnsiStyle annotation.
class ANSIPretty a where
  ansipp :: a -> Doc AnsiStyle

  ansippList :: [a] -> Doc AnsiStyle
  ansippList = align . list . map ansipp

instance Pretty a => ANSIPretty a where
  ansipp = pretty

instance {-# OVERLAPPING #-} ANSIPretty Bind where
  ansipp (Bind n ty ps exp) = pretty n <+> symbol "::" <+> ansipp ty
                              <+> params (symbol "=" <+> ansipp exp)
      where params = if null ps then id else (hsep (map pretty ps) <+>)
  ansippList = vcat . map (<> semi) . map ansipp

instance Pretty Bind where
  pretty = unAnnotate . ansipp

instance {-# OVERLAPPING #-} ANSIPretty Type where
  ansipp = prettyType'
    where
      prettyType (a `Arrow` b) = prettyType' a <+> symbol "->" <+> prettyType b
      prettyType (TypeApp (TypeCon List) b) = blue (brackets (prettyType' b))
      prettyType (TypeApp a b) = prettyType a <+> prettyType'' b
      prettyType (TypeCon Unit) = typecon "()"
      prettyType (TypeCon x)    = typecon $ show x
      prettyType' t@(a `Arrow` b) = parens (prettyType t)
      prettyType' t = prettyType t
      prettyType'' t@(TypeApp a b) = parens (prettyType' t)
      prettyType'' t = prettyType' t

instance {-# OVERLAPPING #-} ANSIPretty Op where
  ansipp Add  = pretty "+"
  ansipp Sub  = pretty "-"
  ansipp Mul  = pretty "*"
  ansipp Quot = pretty "/"
  ansipp Rem  = pretty "%"
  ansipp Neg  = pretty "negate"
  ansipp Gt   = pretty ">"
  ansipp Ge   = pretty ">="
  ansipp Lt   = pretty "<"
  ansipp Le   = pretty "<="
  ansipp Eq   = pretty "=="
  ansipp Ne   = pretty "/="
  ansipp Head = pretty "head"
  ansipp Null = pretty "null"
  ansipp Tail = pretty "tail"

instance {-# OVERLAPPING #-} ANSIPretty Exp where
  ansipp (Var i) = pretty i
  ansipp (App (Prim Neg) e2) = parens (pretty "-" <+> ansipp' e2)
  ansipp (Prim Head) = pretty "head"
  ansipp (Prim Tail) = pretty "tail"
  ansipp (Prim o) = parens (ansipp o)
  ansipp (Con i) = datacon i
  ansipp (Num i) = numeric i
  ansipp (App e1 e2) = ansipp e1 <+> ansipp' e2
  ansipp (If c t e) = keyword "if"
                      <+> align (PP.vsep [ansipp c
                                         , keyword "then" <+> ansipp t
                                         , keyword "else" <+> ansipp e])
  ansipp (Let bs e)  =
    align (PP.vsep [ keyword "let" <+> align (encloseSep mempty semi mempty $ map ansipp bs)
                   , keyword "in" <+> ansipp e])
  ansipp (Recfun b)  = parens (keyword "recfun" <+> ansipp b)

ansipp' t@(App _ _) = parens (ansipp t)
ansipp' t           = ansipp t

instance {-# OVERLAPPING #-} ANSIPretty TypeError where
   ansipp (TypeMismatch t1 t2 e) = PP.vsep [ err "Type mismatch:"
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
