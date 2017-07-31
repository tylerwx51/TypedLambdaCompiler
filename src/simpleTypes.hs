{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SimpleTypes where

import Data.List as List hiding(lookup)
import Data.Map as Map hiding(foldr, foldl', fromList, fold)
import Data.Foldable
import Control.Applicative
import Control.Monad.RWS hiding(fail)
import Control.Monad hiding(fail)
import Control.Arrow (second)
import Prelude hiding (fail, lookup)
import Types

newtype TypeEnv = TEnv (Map String PolyType)

addToEnv :: String -> PolyType -> TypeEnv -> TypeEnv
addToEnv n t (TEnv ts) = TEnv $ singleton n t <> ts

instance Substitable TypeEnv where
  substitute n t (TEnv ts) = TEnv $ fmap (substitute n t) ts

  freeTypeVars (TEnv ts) = foldMap freeTypeVars ts

data InferError = OccursCheck
                | LookupError String
                | UnificationError MonoType MonoType
                deriving(Show)

newtype HM a = HM (RWST TypeEnv () [String] (Either InferError) a) deriving(Functor, Applicative, Monad)

class Monad m => InferMonad m where
  newTVar :: m MonoType
  lookupVar :: String -> m PolyType
  throw :: InferError -> m a
  localEnv :: (TypeEnv -> TypeEnv) -> m a -> m a
  getEnv :: m TypeEnv

instance InferMonad HM where
  newTVar = HM $ do
    (x : xs) <- get
    put xs
    return $ TVar x

  lookupVar n = HM $ do
    (TEnv ts) <- ask
    case lookup n ts of
      Nothing -> lift $ Left $ LookupError n
      Just t -> return t

  throw = HM . lift . Left

  localEnv f (HM ma) = HM $ local f ma

  getEnv = HM ask

localTypeEnv :: InferMonad m => String -> PolyType -> m a -> m a
localTypeEnv n t = localEnv (addToEnv n t)

mkForall :: [String] -> MonoType -> PolyType
mkForall ss m = foldr Forall (T m) ss

generalize :: InferMonad m => MonoType -> m PolyType
generalize mType = do
  envVars <- fmap freeTypeVars getEnv
  let freeVars = freeTypeVars mType
      as = List.filter (`notElem` envVars) freeVars
  return $ mkForall as mType

inst :: InferMonad m => PolyType -> m MonoType
inst poly = do
  let (vars, mono) = unForall poly
  newVars <- mapM (const newTVar) vars
  return $ apply (fromList $ zip vars newVars) mono

unify :: InferMonad m => MonoType -> MonoType -> m Substition
unify (Arrow a1 b1) (Arrow a2 b2) = mappend <$> unify a1 a2 <*> unify b1 b2
unify (TVar n1) (TVar n2)
  | n1 == n2 = return mempty
  | otherwise = return $ fromList [(n1, TVar n2)]
unify (TVar n1) t2
  | n1 `elem` freeTypeVars t2 = throw OccursCheck
  | otherwise = return $ fromList [(n1, t2)]
unify t1 (TVar n2) = unify (TVar n2) t1
unify (TApp ts1) (TApp ts2) = do
  subs <- zipWithM unify ts1 ts2
  return $ fold subs
unify t1 t2 = throw $ UnificationError t1 t2

typeCheck :: Term -> HM (Substition, MonoType)
typeCheck (Apply e1 e2) = do
  (s1, t1) <- typeCheck e1
  (s2, t2) <- localEnv (apply s1) $ typeCheck e2
  tOut <- newTVar
  v <- unify (apply s2 t1) (Arrow t2 tOut)
  return (v <> s2 <> s1, apply v tOut)
typeCheck (Lambda var e) = do
  tIn <- newTVar
  (s1, tOut) <- localTypeEnv var (T tIn) $ typeCheck e
  return (s1, Arrow (apply s1 tIn) tOut)
typeCheck (Let var e1 e2) = do
  (s1, t1) <- typeCheck e1
  p1 <- fmap (apply s1) (generalize t1)
  (s2, t2) <- localEnv (addToEnv var p1 . apply s1) $ typeCheck e2
  return (s2 <> s1, t2)
typeCheck (Var str) = do
  pType <- lookupVar str
  t <- inst pType
  return (mempty, t)

letters :: [String]
letters = fmap return ['a' .. 'z']

uniqueStringList :: [String]
uniqueStringList = letters ++ liftA2 (++) uniqueStringList letters

runHM :: HM (Substition, MonoType) -> Either InferError MonoType
runHM (HM hm) = do
  ((_, res), _, _) <- runRWST hm (TEnv mempty) uniqueStringList
  return res
