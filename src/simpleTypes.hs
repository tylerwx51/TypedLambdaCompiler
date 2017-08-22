{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SimpleTypes where

import Data.List as List hiding(lookup)
import Data.Map as Map hiding(foldr, foldl', fromList, fold)
import qualified Data.Map as Map
import Data.Foldable
import Control.Applicative
import Control.Arrow (second)
import Control.Monad.RWS hiding(fail, Sum)
import Prelude hiding (fail, lookup)
import Types

newtype TypeEnv = TEnv (Map String PolyType) deriving(Monoid)

addToEnv :: String -> PolyType -> TypeEnv -> TypeEnv
addToEnv n t (TEnv ts) = TEnv $ singleton n t <> ts

instance Substitable TypeEnv where
  substitute n t (TEnv ts) = TEnv $ fmap (substitute n t) ts

  freeTypeVars (TEnv ts) = foldMap freeTypeVars ts

data InferError = OccursCheck MonoType MonoType
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

{- a b ~ Either c d
-- a b ~ (Either c) d
-- a ~ Either c, b ~ d
-}

{- b (Fix b) ~ (* ()) a
-- b ~ * ()
-- a ~ Fix (* ())
-}
unify :: InferMonad m => MonoType -> MonoType -> m Substition
unify (TApp t1 t1') (TApp t2 t2') = do
  s1 <- unify t1 t2
  s2 <- unify (apply s1 t1') (apply s1 t2')
  return (s1 <> s2)
unify (TCon str1) (TCon str2)
  | str1 == str2 = return mempty
  | otherwise = throw $ UnificationError (TCon str1) (TCon str2)
unify (TVar n1) (TVar n2)
  | n1 == n2 = return mempty
  | otherwise = return $ fromList [(n1, TVar n2)]
unify (TVar n1) t2
  | n1 `elem` freeTypeVars t2 = throw $ OccursCheck (TVar n1) t2
  | otherwise = return $ fromList [(n1, t2)]
unify t1 (TVar n2) = unify (TVar n2) t1
unify t1 t2 = throw $ UnificationError t1 t2

coerceTo :: InferMonad m => MonoType -> MonoType -> m Substition
coerceTo (TApp t1 t1') (TApp t2 t2') = do
  s1 <- coerceTo t1 t2
  s2 <- coerceTo (apply s1 t1') (apply s1 t2')
  return (s1 <> s2)
coerceTo (TCon str1) (TCon str2)
  | str1 == str2 = return mempty
  | otherwise = throw $ UnificationError (TCon str1) (TCon str2)
coerceTo (TVar n1) (TVar n2)
  | n1 == n2 = return mempty
  | otherwise = return $ fromList [(n1, TVar n2)]
coerceTo (TVar n1) t2
  | n1 `elem` freeTypeVars t2 = throw $ OccursCheck (TVar n1) t2
  | otherwise = return $ fromList [(n1, t2)]
coerceTo t1 t2 = throw $ UnificationError t1 t2

patternType :: InferMonad m => Pattern -> m (MonoType, [(String, MonoType)])
patternType (MatchLeft patt) = do
  (tLeft, newVars) <- patternType patt
  tRight <- newTVar
  return (sumT tLeft tRight, newVars)
patternType (MatchRight patt) = do
  tLeft <- newTVar
  (tRight, newVars) <- patternType patt
  return (sumT tLeft tRight, newVars)
patternType (MatchProd patt1 patt2) = do
  (tLeft, newVars1) <- patternType patt1
  (tRight, newVars2) <- patternType patt2
  return (prod tLeft tRight, newVars1 <> newVars2)
patternType (Otherwise var) = do
  t <- newTVar
  return (t, [(var, t)])
patternType MatchUnit = return (unit, [])
patternType (MatchFix patt) = do
  (tf, newVars) <- patternType patt
  t1 <- newTVar
  t2 <- newTVar
  s1 <- unify tf (TApp t1 t2)
  s2 <- unify (apply s1 t2) (TApp (TCon "Fix") (apply s1 t1))
  return (fixT (apply (s1 <> s2) t1), newVars)

patternLam :: InferMonad m => Pattern -> Term -> m (Substition, MonoType)
patternLam p e = do
  (tIn, newVars) <- patternType p
  (s1, tOut) <- localEnv (TEnv (Map.fromList $ fmap (second T) newVars) <>) $ typeCheck e
  return (s1, arrow (apply s1 tIn) tOut)

caseLam :: InferMonad m => [(Pattern, Term)] -> m (Substition, MonoType)
caseLam [] = return (mempty, TCon "Void")
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
  v <- unify (apply s2 t1) (arrow t2 tOut)
  return (s1 <> s2 <> v, apply v tOut)
typeCheck (Lambda var e) = do
  tIn <- newTVar
  (s1, tOut) <- localTypeEnv var (T tIn) $ typeCheck e
  return (s1, arrow (apply s1 tIn) tOut)
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
typeCheck (Lit (LitInt _)) = return (mempty, TCon "Int")
typeCheck (Lit (LitDouble _)) = return (mempty, TCon "Double")
typeCheck (Coerce term ty) = do
  (s1, t1) <- typeCheck term
  s2 <- coerceTo t1 ty
  return (s1 <> s2, apply s2 t1)

letters :: [String]
letters = fmap return ['a' .. 'z']

uniqueStringList :: [String]
uniqueStringList = letters ++ liftA2 (++) uniqueStringList letters

leftCon :: (String, PolyType)
leftCon = ("Left", Forall "a" $ Forall "b" $ T $ arrow (TVar "a") (sumT (TVar "a") (TVar "b")))

rightCon :: (String, PolyType)
rightCon = ("Right", Forall "a" $ Forall "b" $ T $ arrow (TVar "a") (sumT (TVar "b") (TVar "a")))

pairCon :: (String, PolyType)
pairCon = ("Pair", Forall "a" $ Forall "b" $ T $ arrow (TVar "a") (arrow (TVar "b") (prod (TVar "a") (TVar "b"))))

unitCon :: (String, PolyType)
unitCon = ("Unit", T unit)

decayVoid :: (String, PolyType)
decayVoid = ("absurd", Forall "a" $ T $ arrow (TCon "Void") (TVar "a"))

mkFix :: (String, PolyType)
mkFix = ("MkFix", Forall "f" $ T $ arrow (TApp (TVar "f") (fixT (TVar "f"))) (fixT (TVar "f")))

unFix :: (String, PolyType)
unFix = ("unFix", Forall "f" $ T $ arrow (fixT (TVar "f")) (TApp (TVar "f") (fixT (TVar "f"))))

fixTerm :: (String, PolyType)
fixTerm = ("fix", Forall "a" $ T $ arrow (arrow (TVar "a") (TVar "a")) (TVar "a"))

execHM :: HM (Substition, a) -> Either InferError a
execHM = fmap fst . runHM

runHM :: HM (Substition, a) -> Either InferError (a, Substition)
runHM (HM hm) = do
  ((s, res), _, _) <- runRWST hm (TEnv $ Map.fromList [leftCon, rightCon, pairCon, unitCon, decayVoid, mkFix, unFix, fixTerm]) uniqueStringList
  return (res, s)

data NatHelp a = Z | S a

fixTest :: Term
fixTest = Let "x" (Apply (Var "MkFix") $ Apply (Apply (Var "Pair") (Var "Unit")) (Var "x")) (Var "x")

zTest :: Term
zTest = Apply (Var "MkFix") (Apply (Var "Left") (Var "Unit"))

sTest :: Term
sTest = Lambda "n" $ Apply (Var "MkFix") (Apply (Var "Right") (Var "n"))

natTest :: Term
natTest = Apply sTest (Apply sTest (Apply sTest zTest))

oneTest :: Term
oneTest = Apply sTest zTest

addTest :: Term
addTest = Let "add" (Lambda "x" (Case [(MatchFix (MatchLeft MatchUnit), Var "x"),
                                       (MatchFix (MatchRight (Otherwise "y")),
                                          Apply sTest (Apply (Apply (Var "add") (Var "x")) (Var "y")))]))
                    (Apply (Apply (Var "add") oneTest) natTest)
