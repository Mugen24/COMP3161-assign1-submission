module Hindsight.Syntax where

import Data.List

import MinHS.Syntax(Op(..),TyCon(..))

type Id = String

type Program = CBind

data VExp
    = Num Integer
    | Var Id
    | Thunk CExp
    | Con Id
    deriving (Read, Show, Eq)

{- For the base task, you can assume that Let always contains exactly
     one binding, i.e., looks like this:

         Let [b] c

   In general, you can assume that Recfuns have exactly one argument,
     i.e., look like this:

     Recfun (CBind f ty [x] c)
 -}

data CExp
    = Produce VExp
    | Force VExp
    | Reduce Id CExp CExp
    | Let [VBind] CExp
    | App CExp VExp
    | Recfun CBind
    | Prim Op
    | If VExp CExp CExp
    deriving (Read, Show, Eq)

data CBind = CBind Id CType [Id] CExp
  deriving (Read, Show, Eq)

data VBind = VBind Id VType VExp
  deriving (Read, Show, Eq)

data CType
  = F VType
  | Arrow VType CType
  deriving (Read, Show, Eq, Ord)

data VType
    = TypeCon TyCon
    | TypeApp VType VType
    | U CType
  deriving (Read, Show, Eq, Ord)

binApply :: CExp -> VExp -> VExp -> CExp
binApply e1 e2 e3 = App (App e1 e2) e3
