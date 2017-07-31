module Types where

import Data.List as List hiding(lookup)
import Data.Foldable
import Data.Monoid

data MonoType = TVar String
              | TCon String
              | TApp [MonoType]
              | Arrow MonoType MonoType

showPrec :: Int -> MonoType -> String
showPrec _ (TVar str) = str
showPrec _ (TApp ts) = "[" ++ foldMap (\t -> showPrec 0 t ++ ",") ts ++ "]"
showPrec 0 (Arrow t1 t2) = showPrec 1 t1 ++ "->" ++ showPrec 0 t2
showPrec n (Arrow t1 t2) = "(" ++ showPrec 1 t1 ++ "->" ++ showPrec 0 t2 ++ ")"
showPrec _ (TCon str) = str

instance Show MonoType where
  show = showPrec 0

data PolyType = T MonoType
              | Forall String PolyType
              deriving(Show)

unForall :: PolyType -> ([String], MonoType)
unForall = impl []
  where
    impl vars (T m) = (vars, m)
    impl vars (Forall n p) = impl (vars ++ [n]) p

newtype Substition = Substition [(String, MonoType)] deriving(Show)

fromList :: [(String, MonoType)] -> Substition
fromList = Substition

instance Monoid Substition where
  mempty = Substition []
  mappend (Substition s1) (Substition s2) = Substition $ s1 <> s2

-- Safe in all cases but time complexity O(n^2)
apply' :: Substitable a => Substition -> a -> a
apply' (Substition s) = impl [] s
  where
    impl _ [] v = v
    impl running ((n, t) : ts) v =
      let t' = apply (Substition running) t
          running' = (n, t') : running
          v' = substitute n t v
      in impl running' ts v'

-- Safe only if a variable is never appears after it is substituted
apply :: Substitable a => Substition -> a -> a
apply (Substition s) t = foldl' (\t' (n,r) -> substitute n r t') t s

class Substitable a where
  substitute :: String -> MonoType -> a -> a
  freeTypeVars :: a -> [String]

instance Substitable MonoType where
  substitute n t (TVar str)
    | str == n = t
    | otherwise = TVar str
  substitute n t (TApp ts) = TApp $ fmap (substitute n t) ts
  substitute n t (Arrow t1 t2) = Arrow (substitute n t t1) (substitute n t t2)

  freeTypeVars (TVar str) = [str]
  freeTypeVars (Arrow t1 t2) = freeTypeVars (T t1) ++ freeTypeVars (T t2)
  freeTypeVars (TApp ts) = List.foldl' List.union [] (fmap freeTypeVars ts)

instance Substitable PolyType where
  substitute n t (T m) = T $ substitute n t m
  substitute n t (Forall a p)
    | n == a = Forall a p
    | otherwise = Forall a (substitute n t p)

  freeTypeVars (T mType) = freeTypeVars mType
  freeTypeVars (Forall a pType) = List.delete a (freeTypeVars pType)

data Term = Apply Term Term
          | Let String Term Term
          | Lambda String Term
          | Var String

unLambda :: Term -> ([String], Term)
unLambda (Lambda var term) = let (xs, t) = unLambda term in (var : xs, t)
unLambda t = ([], t)

showPrecT :: Int -> Term -> String
showPrecT _ (Var str) = str
showPrecT 0 (Let var e1 e2) = "let " ++ var ++ " = " ++ showPrecT 0 e1 ++ " in " ++ showPrecT 0 e2
showPrecT 0 e@(Lambda _ _) = let (vars, eIn) = unLambda e in "\\" ++ unwords vars ++ " -> " ++ showPrecT 0 eIn
showPrecT 0 (Apply e1 e2) = showPrecT 0 e1 ++ " " ++ showPrecT 1 e2
showPrecT n e = "(" ++ showPrecT 0 e ++ ")"

instance Show Term where
  show = showPrecT 0