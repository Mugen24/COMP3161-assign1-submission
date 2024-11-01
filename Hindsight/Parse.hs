{-# LANGUAGE RecordWildCards, FlexibleContexts #-}
module Hindsight.Parse where

import qualified Hindsight.Syntax as H

import MinHS.Syntax(Op(..),TyCon(..))

import Text.Parsec
import qualified Text.Parsec.Token as T
import qualified Text.Parsec.Language as L
import Text.Parsec.Expr
import Data.List (foldl1')
import Control.Applicative hiding ( (<|>), many )

type Id = String

data PTree
    = Produce
    | Force
    | Reduce Id PTree PTree
    | Let [PBind] PTree
    | App PTree PTree
    | Recfun PBind
    | Prim Op
    | If PTree PTree PTree
    | Con Id
    | Num Integer
    | Var Id
    | Thunk
    deriving (Read,Show,Eq)

data TTree
  = F
  | Arrow TTree TTree
  | TypeCon TyCon
  | TypeApp TTree TTree
  | U
    deriving (Read,Show,Eq)  

data PBind = PBind Id TTree [Id] PTree
  deriving (Read,Show,Eq)

binApply :: PTree -> PTree -> PTree -> PTree
binApply e1 e2 e3 = App (App e1 e2) e3

parseProgram = parse program

language = L.haskellStyle { T.reservedOpNames = [ "+","-","/","*","%"
                                                , "==","<=",">=","<",">","/="
                                                ,"::","->","\\","=>","="
                                                ]
                          , T.reservedNames   = [ "case","of","let","in","if","then","else"
                                                , "recfun","Int","Bool", "head", "tail"
                                                , "letrec","force","thunk","to","U","F",
                                                  "produce","reduce","negate"
                                                ]
                          , T.identStart      = letter <|> oneOf "_"
                          }

T.TokenParser {..} = T.makeTokenParser language

program = do whiteSpace; v <- bind; eof; return v
  --do whiteSpace; v <- many1 (bind <* semi); eof; return v

bind = PBind <$> varName
              <* reservedOp "::" <*> typ
              <*> many varName <* reservedOp "=" <*> expr
              <?> "binding"

conName = constructor identifier <|> parens (constructor operator) <?> "constructor"
varName = variable identifier <|> parens (variable operator) <?> "variable"
constructor f =  lookAhead isConstructor *> f
variable    f =  isConstructor *> unexpected "Constructor tag where variable expected!"
             <|> f
isConstructor = pure <$> upper <|> string ":"

expr = buildExpressionParser [ [Prefix (App (Prim Neg) <$ reservedOp "-")
                               ]
                             , [Infix (binApply <$> multDivRem) AssocLeft]
                             , [Infix (binApply <$> plusMinus)  AssocLeft]
                             , [Infix (binApply <$> comparison) AssocNone]
                             , [Infix (binApply <$> customOp) AssocNone]
                             ] (foldl1' App <$> many1 term) <?> "expression"
 where op s p = reservedOp s *> pure (Prim p)
       plusMinus  =  op "+" Add
                 <|> op "-" Sub
       multDivRem =  op "*" Mul
                 <|> op "/" Quot
                 <|> op "%" Rem
       comparison =  op ">=" Ge
                 <|> op "<=" Le
                 <|> op "<" Lt
                 <|> op ">" Gt
                 <|> op "==" Eq
                 <|> op "/=" Ne
       customOp = id <$ char '`' <*> conOrVar identifier <* char '`' <* whiteSpace
       conOrVar f =  Con         <$> constructor f
                 <|> Var         <$> f
       term =  If <$ reserved "if" <*> expr <* reserved "then" <*> expr <* reserved "else" <*> expr
           <|> Let    <$ reserved "let"    <*> many1 (bind <* semi) <* reserved "in" <*> expr
           <|> do reserved "reduce"
                  e1 <- expr
                  reserved "to"
                  Var x <- conOrVar identifier
                  reserved "in"
                  e2 <- expr
                  return $ Reduce x e1 e2
           <|> Recfun <$ reserved "recfun" <*> bind

           <|> try (parens (plusMinus
                        <|> multDivRem
                        <|> comparison
                        <|> conOrVar operator
                        <|> pure (Con "()")))
           <|> parens expr
           <|> Num <$> natural
           <|> reserved "force" *> pure Force
           <|> reserved "produce" *> pure Produce
           <|> reserved "thunk" *> pure Thunk
           <|> reserved "head" *> pure (Prim Head)
           <|> reserved "tail" *> pure (Prim Tail)
           <|> reserved "null" *> pure (Prim Null)
           <|> reserved "negate" *> pure (Prim Neg)
           <|> conOrVar identifier
           <?> "term"


typ = buildExpressionParser [ [Infix (whiteSpace *> pure TypeApp) AssocLeft],
                              [Infix (reservedOp "->" *> pure Arrow) AssocRight]
                            ] term <?> "type"
  where term = parens (typ
                   <|> pure (TypeCon Unit))
           <|> reserved "Bool" *> pure (TypeCon Bool)
           <|> reserved "Int"  *> pure (TypeCon Int)
           <|> U <$ reserved "U"
           <|> F <$ reserved "F"
           <|> brackets (TypeApp (TypeCon List) <$> typ)

toCExp :: PTree -> Either String H.CExp
toCExp (Reduce id e1 e2) = H.Reduce id <$> toCExp e1 <*> toCExp e2
toCExp (Let bs e) = H.Let <$> mapM toVBind bs <*> toCExp e
toCExp (App Force e) = H.Force <$> toVExp e
toCExp (App Produce e) = H.Produce <$> toVExp e
toCExp (App e1 e2) = H.App <$> toCExp e1 <*> toVExp e2
toCExp(Recfun b) = H.Recfun <$> toCBind b
toCExp(Prim op) = return $ H.Prim op
toCExp(If b t f) = H.If <$> toVExp b <*> toCExp t <*> toCExp f
toCExp t =
  Left $ concat ["Parse tree conversion failed. Expected computation expression, found:",
                  "\n\n",
                  show t]

apps (App a b) = b:apps a
apps x = [x]

toVExp :: PTree -> Either String H.VExp
toVExp(Num n) = return $ H.Num n
toVExp(Var id) = return $ H.Var id
toVExp(Con id) = return $ H.Con id
toVExp(App Thunk e) = H.Thunk <$> toCExp e
toVExp t =
  Left $ concat ["Parse tree conversion failed. Expected value expression, found:",
                  "\n\n",
                  show t]

toCBind :: PBind -> Either String H.CBind
toCBind(PBind x ty vs e) =
  H.CBind <$> pure x <*> toCType ty <*> pure vs <*> toCExp e

toVBind :: PBind -> Either String H.VBind
toVBind(PBind x ty [] e) =
  H.VBind <$> pure x <*> toVType ty <*> toVExp e
toVBind(PBind x ty _ e) =
  Left $ concat ["Parse tree conversion failed. Value binding for ",
                  x," cannot have parameters."]

toCType :: TTree -> Either String H.CType
toCType(TypeApp F t) = H.F <$> toVType t
toCType(Arrow t1 t2) = H.Arrow <$> toVType t1 <*> toCType t2
toCType t =
  Left $ concat ["Parse tree conversion failed. Expected computation type, found:",
                  "\n\n",
                  show t]

toVType :: TTree -> Either String H.VType
toVType(TypeCon c) = return $ H.TypeCon c
toVType(TypeApp U t) = H.U <$> toCType t
toVType(TypeApp t1 t2) = H.TypeApp <$> toVType t1 <*> toVType t2
toVType t =
  Left $ concat ["Parse tree conversion failed. Expected value type, found:",
                 "\n\n",
                 show t]
