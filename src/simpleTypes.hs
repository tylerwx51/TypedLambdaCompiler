{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SimpleTypes where

import Data.List as List hiding(lookup)
import Data.Map as Map hiding(foldr, foldl', fromList, fold)
import qualified Data.Map as Map
import Data.Foldable
import Control.Applicative
import Control.Monad.RWS hiding(fail, Sum)
import Prelude hiding (fail, lookup)
import Types

newtype TypeEnv = TEnv (Map String PolyType) deriving(Monoid)

addToEnv :: String -> PolyType -> TypeEnv -> TypeEnv
addToEnv n t (TEnv ts) = TEnv $ singleton n t <> ts

instance Substitable TypeEnv where
  substitute n t (TEnv ts) = TEnv $ fmap (substitute n t) ts

  freeTypeVars (TEnv ts) = foldMap freeTypeVars ts

data InferError = OccursCheck
                | LookupError String
                | UnificationError MonoType MonoType
                | EmptyCase
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

unifyApp :: (InferMonad m) => (MonoType, MonoType) -> (MonoType, MonoType) -> m Substition
unifyApp (a1, a2) (b1, b2) = do
  s1 <- unify a1 a2
  s2 <- unify (apply s1 b1) (apply s1 b2)
  return $ s1 <> s2

unify :: InferMonad m => MonoType -> MonoType -> m Substition
unify (Arrow a1 b1) (Arrow a2 b2) = unifyApp (a1, a2) (b1, b2)
unify (Prod a1 b1) (Prod a2 b2) = unifyApp (a1, a2) (b1, b2)
unify (Sum a1 b1) (Sum a2 b2) = unifyApp (a1, a2) (b1, b2)
unify Unit Unit = return mempty
unify Void Void = return mempty
unify (TVar n1) (TVar n2)
  | n1 == n2 = return mempty
  | otherwise = return $ fromList [(n1, TVar n2)]
unify (TVar n1) t2
  | n1 `elem` freeTypeVars t2 = throw OccursCheck
  | otherwise = return $ fromList [(n1, t2)]
unify t1 (TVar n2) = unify (TVar n2) t1
unify t1 t2 = throw $ UnificationError t1 t2

patternType :: InferMonad m => Pattern -> m (MonoType, [(String, MonoType)])
patternType (MatchLeft patt) = do
  (tLeft, newVars) <- patternType patt
  tRight <- newTVar
  return (Sum tLeft tRight, newVars)
patternType (MatchRight patt) = do
  tLeft <- newTVar
  (tRight, newVars) <- patternType patt
  return (Sum tLeft tRight, newVars)
patternType (MatchProd patt1 patt2) = do
  (tLeft, newVars1) <- patternType patt1
  (tRight, newVars2) <- patternType patt2
  return (Prod tLeft tRight, newVars1 ++ newVars2)
patternType (Otherwise var) = do
  t <- newTVar
  return (t, [(var, t)])
patternType MatchUnit = return (Unit, [])

patternLam :: InferMonad m => Pattern -> Term -> m (Substition, MonoType)
patternLam p e = do
  (tIn, newVars) <- patternType p
  (s1, tOut) <- localEnv (TEnv (Map.fromList $ fmap (\(a, b) -> (a, T b)) newVars) <>) $ typeCheck e
  return (s1, Arrow (apply s1 tIn) tOut)

caseLam :: InferMonad m => [(Pattern, Term)] -> m (Substition, MonoType)
caseLam [] = throw EmptyCase
caseLam [(p, t)] = patternLam p t
caseLam ((p, t):xs) = do
  (s1, t1) <- patternLam p t
  (s2, t2) <- localEnv (apply s1) $ caseLam xs
  v <- unify (apply s2 t1) t2
  return (s1 <> s2 <> v, apply v t2)

typeCheck :: (InferMonad m) => Term -> m (Substition, MonoType)
typeCheck (Apply e1 e2) = do
  (s1, t1) <- typeCheck e1
  (s2, t2) <- localEnv (apply s1) $ typeCheck e2
  tOut <- newTVar
  v <- unify (apply s2 t1) (Arrow t2 tOut)
  return (s1 <> s2 <> v, apply v tOut)
typeCheck (Lambda var e) = do
  tIn <- newTVar
  (s1, tOut) <- localTypeEnv var (T tIn) $ typeCheck e
  return (s1, Arrow (apply s1 tIn) tOut)
typeCheck (Let var e1 e2) = do
  newVar <- newTVar
  (s1, t1) <- localEnv (addToEnv var (T newVar)) $ typeCheck e1
  v <- unify (apply s1 newVar) t1
  p1 <- localEnv (apply (s1 <> v)) $ generalize (apply v t1)
  (s2, t2) <- localEnv (addToEnv var p1 . apply (s1 <> v)) $ typeCheck e2
  return (s1 <> v <> s2, t2)
typeCheck (Var str) = do
  pType <- lookupVar str
  t <- inst pType
  return (mempty, t)
typeCheck (Case es) = caseLam es

letters :: [String]
letters = fmap return ['a' .. 'z']

uniqueStringList :: [String]
uniqueStringList = letters ++ liftA2 (++) uniqueStringList letters

leftCon :: (String, PolyType)
leftCon = ("Left", Forall "a" $ Forall "b" $ T $ Arrow (TVar "a") (Sum (TVar "a") (TVar "b")))

rightCon :: (String, PolyType)
rightCon = ("Right", Forall "a" $ Forall "b" $ T $ Arrow (TVar "a") (Sum (TVar "b") (TVar "a")))

pairCon :: (String, PolyType)
pairCon = ("Pair", Forall "a" $ Forall "b" $ T $ Arrow (TVar "a") (Arrow (TVar "b") (Prod (TVar "a") (TVar "b"))))

unitCon :: (String, PolyType)
unitCon = ("Unit", T Unit)

execHM :: HM (Substition, MonoType) -> Either InferError MonoType
execHM = fmap fst . runHM

runHM :: HM (Substition, MonoType) -> Either InferError (MonoType, Substition)
runHM (HM hm) = do
  ((s, res), _, _) <- runRWST hm (TEnv $ Map.fromList [leftCon, rightCon, pairCon, unitCon]) uniqueStringList
  return (res, s)
