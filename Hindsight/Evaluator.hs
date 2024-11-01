module Hindsight.Evaluator where

import Data.List
import qualified MinHS.Env as E
import Hindsight.Syntax
import MinHS.Syntax(Op(..),TyCon(..))

import MinHS.Pretty(datacon,numeric,ANSIPretty(..))
import Prettyprinter as PP
import Prettyprinter.Render.Terminal


instance {-# OVERLAPPING #-} ANSIPretty Value where
  ansipp (I i) = numeric $ i
  ansipp (B b) = datacon $ show b
  ansipp (Nil) = datacon "Nil"
  ansipp (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> ansipp v)
  ansipp _ = undefined -- should not ever be used

instance Pretty Value where
  pretty = unAnnotate . ansipp

type VEnv = E.Env Value

evaluate :: CBind -> Value
evaluate (CBind _ _ _ e) =
  case evalC E.empty e of
    P v -> v
    _   -> error "Top-level computation produced non-ground value"

--- From here is where you should put your work!

data Value = I Integer
           | B Bool
           | Nil
           | Cons Integer Value
           | V String
           | Sus VEnv CExp
           -- TODO: others as needed
           deriving (Show)

data Terminal =
           P Value
           -- TODO: others as needed

consTail :: Value -> Value
consTail (Cons num Nil) = I num
consTail (Cons _ v) = consTail v
consTail _ = undefined

evalV :: VEnv -> VExp -> Value
evalV _ (Num n) = I n
evalV _ (Con "True") = B True
evalV _ (Con "False") = B False
evalV e (Var x) = 
  case E.lookup e x of
    Just y -> y
    Nothing -> error "Accessing undefined variable"

evalV _ (Con "Nil" ) = Nil
evalV e (Thunk cexpr) = Sus e cexpr
evalV _ _ = error "TODO: implement evalV"


evalC :: VEnv -> CExp -> Terminal
evalC e (Produce v1) = 
  let v2 = evalV e v1
  in P v2

evalC e (If vexpr c1 c2) = 
  let outcome = evalV e vexpr
  in
    case outcome of 
      (B True) -> 
        evalC e c1
      (B False) -> 
        evalC e c2
      _ -> error "vexpr did not resolve to bool"



evalC e (Force vexpr) = 
  let 
    v1 = evalV e vexpr
  in
    case v1 of
      -- cexpr evaluate further
      (Sus e1 cexpr) -> 
        evalC e1 cexpr
      _ -> 
        P $ evalV e vexpr

  
evalC e (Reduce id1 cexpr1 cexpr2) = 
  let 
    (P v1) = evalC e cexpr1
    newEnv = E.add e (id1, v1)
  in 
    v1 
    `seq`
    evalC newEnv cexpr2


evalC e ref@(Let (vbind:rest) cexpr) =
  let 
    (VBind id1 _ vexpr) = vbind
    newEnv = E.add e (id1, evalV e vexpr)

  in
    case rest of 
      [] -> evalC newEnv cexpr
      _  -> evalC newEnv (Let rest cexpr)




-- Binary Operator
evalC e ref@(App (Prim x) vexpr) = 
  let 
    v1 = evalV e vexpr
  in
    case x of 
      Head -> 
        case v1 of 
          Nil -> error "List empty"
          (Cons num _) -> P (I num)
          _ -> error "Should be a list"

      Tail -> 
        case v1 of 
          Nil -> error "List empty"
          (Cons _ myTail) -> P myTail
          _ -> error "Should be a list"
      
      Neg -> 
        case v1 of 
          (I num)   -> P (I (-num))
          _         -> error $ "Negating no integer: " ++ show v1

      Null -> 
        case v1 of 
          Nil -> P (B True)
          (Cons _ _) -> P (B False)
          _ -> error $ "Null check non array: " ++ show v1

      _ -> 
        -- Return the closure of Prim for the outer var to evaluate
        P (Sus e (App (Prim x) vexpr))


-- Unary Operator
evalC e ref@(App (App (Prim x) vexpr1) vexpr2) = 
  let 
    v1 = evalV e vexpr1
    v2 = evalV e vexpr2
    v1' = 
      case v1 of 
        (I n) -> n
        _     -> error "Value not an Int"

    v2' = 
      case v2 of 
        (I n) -> n
        _     -> error "Value not an Int"

  in
    case Prim x of 
      (Prim Sub) -> P(I (v1' - v2'))
      (Prim Add) -> P(I (v1' + v2'))
      (Prim Mul) -> P(I (v1' * v2'))
      (Prim Quot) -> 
        if v2' == 0 then error "Division by zero"
        else P(I (v1' `div` v2'))

      (Prim Rem) -> P(I (v1' `rem` v2'))
      (Prim Gt) -> 
        if v1' > v2' then
          P (B True)
        else 
          P (B False)
      (Prim Ge) -> 
        if v1' >= v2' then P (B True)
                  else P (B False)
      (Prim Lt) -> 
        if v1' < v2' then P (B True)
                  else P (B False)
      (Prim Le) -> 
        if v1' <= v2' then P (B True)
                  else P (B False)
      (Prim Eq) -> 
        if v1' == v2' then P (B True)
                  else P (B False)
      -- Not equal
      (Prim Ne) -> 
        if v1' /= v2' then P (B True)
                  else P (B False)
      _ -> error "Unhandled case"



evalC e (App (Force (Con "Cons")) vexpr1) = 
  P (Sus e (App (Force (Con "Cons")) vexpr1))

-- Concatenate
evalC e (App (App (Force (Con "Cons")) vexpr1) vexpr2) = 
  let 
    v1 = evalV e vexpr1
    v2 = evalV e vexpr2
    v1' = 
      case v1 of 
        (I n) -> n
        _     -> error "Value not an Int"

    v2' = 
      case v2 of 
        (I n) -> n
        _     -> error "Value not an Int"

  in
    P (Cons v1' v2)


evalC e reg@(Recfun (CBind id1 _ _ cexpr))= 
    P (Sus e reg)


evalC e ref@(App cexpr vexpr) = 
  let 
    v1 = evalV e vexpr
    -- Can also be Nil

    P c1 = evalC e cexpr
  in
    case c1 of
      func@(Sus e1 (Recfun (CBind funcName funcType [param] funcBody))) -> 
        let 
          newEnv = E.addAll e1 [(param, v1), (funcName, func)]
        in
          evalC newEnv funcBody
      
      -- Requires another param
      func@(Sus e1 cexpr1) ->
        case v1 of 
          (I num) -> evalC e1 (App cexpr1 (Num num))
          Nil -> evalC e1 (App cexpr1 (Con "Nil"))

      _ -> 
        error "wot"


evalC g y = 
  error "TODO: implement evalC"
 