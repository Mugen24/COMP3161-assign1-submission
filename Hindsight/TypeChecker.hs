{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections #-}
module Hindsight.TypeChecker where

import qualified MinHS.Env as E
import Hindsight.Syntax
import MinHS.Syntax(Op(..),TyCon(..))

import Control.Applicative
import Control.Monad (void, unless)
import Control.Monad.Fail
import MinHS.TypeChecker(tyConKind,Kind(..))

type Gamma = E.Env VType

primOpType :: Op -> CType
primOpType Head = TypeApp (TypeCon List) (TypeCon Int) `Arrow` F(TypeCon Int)
primOpType Null = TypeApp (TypeCon List) (TypeCon Int) `Arrow` F(TypeCon Bool)
primOpType Tail = TypeApp (TypeCon List) (TypeCon Int) `Arrow` F(TypeApp (TypeCon List) (TypeCon Int))
primOpType Gt   = TypeCon Int `Arrow` (TypeCon Int `Arrow` F(TypeCon Bool))
primOpType Ge   = TypeCon Int `Arrow` (TypeCon Int `Arrow` F(TypeCon Bool))
primOpType Lt   = TypeCon Int `Arrow` (TypeCon Int `Arrow` F(TypeCon Bool))
primOpType Le   = TypeCon Int `Arrow` (TypeCon Int `Arrow` F(TypeCon Bool))
primOpType Eq   = TypeCon Int `Arrow` (TypeCon Int `Arrow` F(TypeCon Bool))
primOpType Ne   = TypeCon Int `Arrow` (TypeCon Int `Arrow` F(TypeCon Bool))
primOpType Neg  = TypeCon Int `Arrow` F(TypeCon Int)
primOpType _    = TypeCon Int `Arrow` (TypeCon Int `Arrow` F(TypeCon Int))

constructorType :: Id -> Maybe VType
constructorType "Nil"   = Just $ TypeApp (TypeCon List) (TypeCon Int)
constructorType "True"  = Just $ TypeCon Bool
constructorType "False" = Just $ TypeCon Bool
constructorType "Cons" =
     Just . U $ TypeCon Int
    `Arrow` (TypeApp (TypeCon List) (TypeCon Int)
    `Arrow` F(TypeApp (TypeCon List) (TypeCon Int)))
constructorType _ = Nothing

initialGamma :: Gamma
initialGamma = E.empty

data TypeError = TypeMismatch CType CType CExp
               | VTypeMismatch VType VType VExp
               | TypeShouldBeFunction CType CBind
               | FunctionTypeExpected CExp CType
               | NoSuchVariable Id
               | NoSuchConstructor Id
               | ForceNonThunk VType VExp
               | Unreducible CType CExp
               | TypeConstructorSaturated VType Kind
               | KindMismatch Kind Kind VType
               deriving (Show)

newtype TC a = TC (Either TypeError a) deriving (Monad, Functor, Applicative)

instance MonadFail TC where
   fail = error 
 
runTC :: TC () -> Maybe TypeError
runTC (TC (Left err)) = Just err
runTC (TC (Right ())) = Nothing

typeError :: TypeError -> TC a
typeError = TC . Left

typecheck :: Program -> Maybe TypeError
typecheck = runTC . void . checkCBinds initialGamma . (:[])

checkCBinds :: Gamma -> [CBind] -> TC Gamma
checkCBinds g (b:bs) = (E.add g . fmap U <$> checkCBind g b) >>= flip checkCBinds bs
checkCBinds g []     = return g

checkVBinds :: Gamma -> [VBind] -> TC Gamma
checkVBinds g (b:bs) = (E.add g <$> checkVBind g b) >>= flip checkVBinds bs
checkVBinds g []     = return g

checkCBinds' :: Gamma -> [CBind] -> TC ()
checkCBinds' g (b:bs) = checkCBind g b >> checkCBinds' g bs
checkCBinds' g []     = return ()

checkVBind :: Gamma -> VBind -> TC (Id, VType)
checkVBind g b@(VBind n ty exp) = do ty `ofKind` Star
                                     shouldCheck' g exp ty
                                     return (n,ty)

checkCBind :: Gamma -> CBind -> TC (Id, CType)
checkCBind g b@(CBind n ty args exp) = do cTypeWellformed ty
                                          checkAbs g b
                                          return (n,ty)

checkAbs :: Gamma -> CBind -> TC ()
checkAbs g   (CBind n (Arrow a b) (x:xs) exp) = checkAbs (g `E.add` (x,a)) (CBind n b xs exp)
checkAbs g b@(CBind n ty          (x:xs) _  ) = typeError $ TypeShouldBeFunction ty b
checkAbs g   (CBind n ty          []     exp) = shouldCheck g exp ty

shouldCheck :: Gamma -> CExp -> CType -> TC ()
shouldCheck g exp t
  = do t' <- checkComputation g exp
       unless (t' == t) $ typeError $ TypeMismatch t t' exp

shouldCheck' :: Gamma -> VExp -> VType -> TC ()
shouldCheck' g exp t
  = do t' <- checkValue g exp
       unless (t' == t) $ typeError $ VTypeMismatch t t' exp

typeWellformed :: VType -> TC Kind
typeWellformed (TypeCon c) = return $ tyConKind c
typeWellformed (TypeApp a b)
  = do kb :=> kr <- expectArrowKind typeWellformed a
       b `ofKind` kb
       return kr
  where expectArrowKind a t
          = do x <- a t
               case x of
                 a :=> b -> return x
                 _       -> typeError $ TypeConstructorSaturated t x
typeWellformed (U ty) = Star <$ cTypeWellformed ty

cTypeWellformed :: CType -> TC ()
cTypeWellformed (F ty) = () <$ ty `ofKind` Star
cTypeWellformed (Arrow a b) = (a `ofKind` Star) >> cTypeWellformed b

ofKind t k = do k' <- typeWellformed t
                unless (k == k') $ typeError $ KindMismatch k k' t


checkValue :: Gamma -> VExp -> TC VType
checkValue g (Var i)  | Just t <- E.lookup g i = return t
                    | otherwise              = typeError $ NoSuchVariable i
checkValue g (Num _) = return $ TypeCon Int
checkValue g (Con c)  | Just t <- constructorType c = return t
                       | otherwise           = typeError $ NoSuchConstructor c
checkValue g (Thunk v) = U <$> checkComputation g v


checkComputation :: Gamma -> CExp -> TC CType
checkComputation g (Prim c) | t <- primOpType c = return t
checkComputation g (Produce v) = F <$> checkValue g v
checkComputation g (Reduce x e1 e2) =
  do
    cty <- checkComputation g e1
    case cty of
      F vty -> checkComputation (E.add g (x,vty)) e2
      cty   -> typeError $ Unreducible cty e1

checkComputation g (Force v) = do
  vty <- checkValue g v
  case vty of
    U cty -> return $ cty
    _ -> typeError $ ForceNonThunk vty v
checkComputation g (App e1 e2)
  = do a `Arrow` b <- expectFunctionType (checkComputation g) e1
       shouldCheck' g e2 a
       return b
  where expectFunctionType :: (CExp -> TC CType) -> (CExp -> TC CType)
        expectFunctionType a e
          = do x <- a e
               case x of
                 a `Arrow` b -> return x
                 _           -> typeError $ FunctionTypeExpected e x
checkComputation g (If c t e)
  = do shouldCheck' g c (TypeCon Bool)
       t1 <- checkComputation g t
       shouldCheck g e t1
       return t1
checkComputation g (Let bs e) = checkVBinds g bs >>= flip checkComputation e
checkComputation g (Recfun b@(CBind n ty ps e))
  = do cTypeWellformed ty
       checkAbs (g `E.add` (n, U ty)) b
       return ty

