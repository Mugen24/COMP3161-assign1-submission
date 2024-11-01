module MinHS.Evaluator where

import MinHS.Syntax

import qualified Hindsight.CBNCompile as N
import qualified Hindsight.CBVCompile as V
import qualified Hindsight.Evaluator as E

evaluate :: Bool -> Program -> E.Value
evaluate cbn prog = E.evaluate $ compiler prog
  where compiler | cbn       = N.compileProgram
                 | otherwise = V.compileProgram
