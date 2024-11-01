module Hindsight.CBVCompile where

import qualified Hindsight.Syntax as T
import qualified MinHS.Syntax as M
import qualified MinHS.Env as E
import qualified MinHS.TypeChecker as TC

import Data.Maybe(fromJust)

retTy :: M.Type -> T.CType
retTy (_ `M.Arrow` (ty `M.Arrow` ty')) =
  T.Arrow (compileVType ty) (compileCType ty')

consRetTy = retTy . fromJust . TC.constructorType $ "Cons" 

primOpRetTy :: M.Op -> T.CType
primOpRetTy = retTy . TC.primOpType

escape :: String -> String
escape xs = '_':xs

compileProgram (M.Bind f ty xs e) = T.CBind f (compileCType ty) xs (compileC e)

compileArrowType (M.Arrow t1 t2) =
  T.Arrow (compileVType t1) (compileCType t2)
compileArrowType t = compileCType t

compileCType :: M.Type -> T.CType
compileCType ty = T.F(compileVType ty)
compileVType :: M.Type -> T.VType
compileVType (M.Arrow t1 t2) =
  T.U (T.Arrow (compileVType t1) (compileCType t2))
compileVType (M.TypeCon t) = T.TypeCon t
compileVType (M.TypeApp t1 t2) = T.TypeApp (compileVType t1) (compileVType t2)

compileC :: M.Exp -> T.CExp
compileC (M.App e1 e2) =
  T.Reduce "x" (compileC e2)
  $ T.Reduce "f" (compileC e1)
  $ (T.App (T.Force $ T.Var "f") (T.Var "x"))
compileC (M.Num n) = T.Produce(T.Num n)
compileC (M.Var x) =
  T.Produce $ T.Var $ escape x
compileC (M.Prim M.Neg) =
  T.Produce $ T.Thunk $ T.Prim M.Neg
compileC (M.Prim M.Null) =
  T.Produce $ T.Thunk $ T.Prim M.Null
compileC (M.Prim M.Tail) =
  T.Produce $ T.Thunk $ T.Prim M.Tail
compileC (M.Prim M.Head) =
  T.Produce $ T.Thunk $ T.Prim M.Head
compileC (M.Prim op) =
  T.Produce $ T.Thunk
  $ (T.Recfun (T.CBind "f" (compileArrowType $ TC.primOpType op) ["x"]
                (T.Produce $ T.Thunk $ T.App (T.Prim op) (T.Var "x"))))
compileC (M.If b t f) =
  T.Reduce "x" (compileC b) (T.If (T.Var "x") (compileC t) (compileC f))
compileC (M.Con xs)
  | xs `elem` ["Nil","True","False"] = T.Produce $ T.Con xs
  | xs == "Cons" =
  T.Produce $ T.Thunk
  $ (T.Recfun (T.CBind "f" (compileArrowType . fromJust . TC.constructorType $ "Cons") ["x"]
                (T.Produce $ T.Thunk $ T.App (T.Force $ T.Con "Cons") (T.Var "x"))))
compileC (M.Let [] e) = compileC e
compileC (M.Recfun (M.Bind f ty xs e)) =
  T.Produce $ T.Thunk $
  T.Recfun (T.CBind (escape f) (compileArrowType ty) (map escape xs)
                    (compileC e))
compileC (M.Let (M.Bind x ty [] e1:xs) e2) =
  T.Reduce
    (escape x)
    (compileC e1)
    (compileC (M.Let xs e2))
compileC xs =
  error $ show xs
