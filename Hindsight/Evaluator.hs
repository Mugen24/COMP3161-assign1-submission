module Hindsight.Evaluator where

import Data.List
import qualified MinHS.Env as E
import Hindsight.Syntax
import MinHS.Syntax(Op(..),TyCon(..))

import MinHS.Pretty(datacon,numeric,ANSIPretty(..))
import Prettyprinter as PP
import Prettyprinter.Render.Terminal

import Debug.Trace
import Text.Printf

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
  trace ("Var: " ++ show x ++ "\n")
  $
  case E.lookup e x of
    Just y -> trace (show y ++ "\n") y
    Nothing -> 
      trace ("undefined var" ++ show x ++ "\n" ++ show e) 
      (error "Accessing undefined variable")

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
        -- trace ("If false: " ++ show e)
        evalC e c2
      _ -> error "vexpr did not resolve to bool"



evalC e (Force vexpr) = 
  let 
    v1 = evalV e vexpr
  in
    case v1 of
      -- cexpr evaluate further
      (Sus e1 cexpr) -> 
        -- trace (
        --   "Force: vexpresion: " ++ show vexpr ++ "\n" ++
        --   "Force: evaluated vexpresion: " ++ show (evalV e vexpr)
        -- )
        evalC e1 cexpr
      -- Nothing more to evaluate
      _ -> 
        -- trace (
        --   "Force: vexpresion: " ++ show vexpr ++ "\n" ++
        --   "Force: evaluated vexpresion: " ++ show (evalV e vexpr)
        -- )
        P $ evalV e vexpr
  -- let 
  --   v1 = evalV e vexpr
  -- in 
  --   case v1 of
  --     (Sus e1 cexpr) -> evalC e cexpr -- TODO: have to be e otherwise args is not defined
  --     _ -> error "not a closure"

  
-- TODO: for some reason id shadows existing var so id1
evalC e (Reduce id1 cexpr1 cexpr2) = 
  -- trace ("REDUCE: \n" ++ 
  --   "  cexpr1: " ++ show cexpr1 ++ "\n" ++
  --   "  cexpr2: " ++ show cexpr2 
  -- )
  -- $
  let 
    (P v1) = evalC e cexpr1
    newEnv = E.add e (id1, v1)
  in 
    -- trace (show v1)
    -- $
    v1 
    `seq`
    evalC newEnv cexpr2


evalC e ref@(Let (vbind:rest) cexpr) =
  -- trace ("Param: " ++ show ref ++ "\n")
  -- $
  let 
    (VBind id1 _ vexpr) = vbind
    newEnv = E.add e (id1, evalV e vexpr)

  in
    case rest of 
      [] -> evalC newEnv cexpr
      _  -> evalC newEnv (Let rest cexpr)




-- Binary Operator
evalC e ref@(App (Prim x) vexpr) = 
  -- trace ("Param: " ++ show ref ++ "\n")
  -- $
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
        trace ("Shouldn't happen: Prim " ++ show x)
        -- Return the closure of Prim for the outer var to evaluate
        P (Sus e (App (Prim x) vexpr))


-- Unary Operator
evalC e ref@(App (App (Prim x) vexpr1) vexpr2) = 
  -- trace (
  --   "Applicator primitive: \n" 
  --   )
  -- $
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
        trace ("Quote /n v1: " ++ show v1 ++ "v2: " ++ show v2)
        $
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
      _ -> 
        trace ("Shouldn't happen: " ++ show ref)
        $
        error "Unhandled case"
        -- P Nil



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
    -- trace ("Recfun: " ++ show id1)
    P (Sus e reg)


evalC e ref@(App cexpr vexpr) = 
  trace (
    "Query: " ++ show ref ++ "\n" ++
    "App:\n" ++ 
    "E: \n" ++ show e ++ "\n" ++
    "cexpr: " ++ show cexpr ++ "\n" ++
    "vexpr: " ++ show vexpr ++ "\n"
  )
  $
  let 
    v1 = evalV e vexpr
    -- Can also be Nil

    P c1 = evalC e cexpr
  in
    trace (
      printf "v1: %s \n\
             \c1: %s\n" (show v1) (show c1) 
    )
    $ 
    case c1 of
      func@(Sus e1 (Recfun (CBind funcName funcType [param] funcBody))) -> 
        let 
          newEnv = E.addAll e1 [(param, v1), (funcName, func)]
        in
          trace ("App Recfunc " ++ show c1 ++ " " ++ show v1)
          evalC newEnv funcBody
      
      -- Requires another param
      func@(Sus e1 cexpr1) ->
        -- trace (
        --   "App other Recfunc: evalC " ++ show e1 ++ " (App " ++ show cexpr1 ++ " " ++ show vexpr ++")"
        -- )
        -- $
        -- Can't pass vexpr like this 
        -- Some can only be evaluated at e
        -- Need to fully evaluate v1 to Num or Con ??
        -- evalC e1 (App cexpr1 (Num num))
        -- let 
        --   (E.Env n1) = e
        --   (E.Env n2) = e1
        --   newEnv = E.Env (M.union n2 n1)
        -- in
        case v1 of 
          (I num) -> evalC e1 (App cexpr1 (Num num))
          Nil -> evalC e1 (App cexpr1 (Con "Nil"))
        -- evalC e1 (App c1 (Num num))
        -- evalC e1 (App cexpr1 vexpr)
        -- evalC newEnv (App cexpr1 vexpr)

      _ -> 
        trace ("Unhandled: App " ++ show c1 ++ " " ++ show v1)
        error "wot"


evalC g y = 
  trace ("calling evalc with g = " ++ show g ++ " ; y = " ++ show y) 
  error "TODO: implement evalC"
 