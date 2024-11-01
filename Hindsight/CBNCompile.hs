module Hindsight.CBNCompile where

import qualified Hindsight.Syntax as T
import qualified MinHS.Syntax as M
import qualified MinHS.Env as E
import qualified MinHS.TypeChecker as TC

import Data.Maybe(fromJust)

compileProgram (M.Bind f ty xs e) = T.CBind f (compileCType ty) xs (compileC e)

compileCType :: M.Type -> T.CType
compileCType _ = error "TODO: implement compileCType"

compileVType :: M.Type -> T.VType
compileVType _ = error "TODO: implement compileVType"

compileC :: M.Exp -> T.CExp
compileC _ = error "TODO: implement compileC"
