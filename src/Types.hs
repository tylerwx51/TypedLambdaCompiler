module Types where

import Data.List as List hiding(lookup)
import Data.Monoid hiding(Sum)

data MonoType = TVar String
              | TCon String
              | Arrow MonoType MonoType
              | Prod MonoType MonoType
              | Sum MonoType MonoType

showPrec :: Int -> MonoType -> String
showPrec _ (TVar str) = str
showPrec _ (TCon str) = str
showPrec 0 (Arrow t1 t2) = showPrec 1 t1 ++ " -> " ++ showPrec 0 t2
showPrec 0 (Prod t1 t2) = showPrec 0 t1 ++ " * " ++ showPrec 1 t2
showPrec 0 (Sum t1 t2) = showPrec 0 t1 ++ " + " ++ showPrec 1 t2
showPrec _ t = "(" ++ showPrec 0 t ++ ")"

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
  substitute n t (Arrow t1 t2) = Arrow (substitute n t t1) (substitute n t t2)
  substitute n t (Prod t1 t2) = Prod (substitute n t t1) (substitute n t t2)
  substitute n t (Sum t1 t2) = Sum (substitute n t t1) (substitute n t t2)
  substitute _ _ (TCon t) = TCon t

  freeTypeVars (TVar str) = [str]
  freeTypeVars (TCon _) = []
  freeTypeVars (Arrow t1 t2) = freeTypeVars (T t1) ++ freeTypeVars (T t2)
  freeTypeVars (Prod t1 t2) = freeTypeVars (T t1) ++ freeTypeVars (T t2)
  freeTypeVars (Sum t1 t2) = freeTypeVars (T t1) ++ freeTypeVars (T t2)

instance Substitable PolyType where
  substitute n t (T m) = T $ substitute n t m
  substitute n t (Forall a p)
    | n == a = Forall a p
    | otherwise = Forall a (substitute n t p)

  freeTypeVars (T mType) = freeTypeVars mType
  freeTypeVars (Forall a pType) = List.delete a (freeTypeVars pType)

data Pattern = MatchLeft Pattern
             | MatchRight Pattern
             | MatchProd Pattern Pattern
             | Otherwise String

instance Show Pattern where
  show (MatchLeft patt) = "Left (" ++ show patt ++ ")"
  show (MatchRight patt) = "Right (" ++ show patt ++ ")"
  show (MatchProd patt1 patt2) = "(" ++ show patt1 ++ ", " ++ show patt2 ++ ")"
  show (Otherwise x) = x

varList :: Pattern -> [String]
varList (MatchLeft patt) = varList patt
varList (MatchRight patt) = varList patt
varList (MatchProd patt1 patt2) = varList patt1 ++ varList patt2
varList (Otherwise t) = [t]

data Term = Apply Term Term
          | Let String Term Term
          | Lambda String Term
          | Case [(Pattern, Term)]
          | Var String

unLambda :: Term -> ([String], Term)
unLambda (Lambda var term) = let (xs, t) = unLambda term in (var : xs, t)
unLambda t = ([], t)

showCase :: (Pattern, Term) -> String
showCase (p, e) = show p ++ " -> " ++ show e

showPrecT :: Int -> Term -> String
showPrecT _ (Var str) = str
showPrecT 0 (Let var e1 e2) = "let " ++ var ++ " = " ++ showPrecT 0 e1 ++ " in " ++ showPrecT 0 e2
showPrecT 0 e@(Lambda _ _) = let (vars, eIn) = unLambda e in "\\" ++ unwords vars ++ " -> " ++ showPrecT 0 eIn
showPrecT 0 (Apply e1 e2) = showPrecT 0 e1 ++ " " ++ showPrecT 1 e2
showPrecT 0 (Case es) = "Case \n" ++ unlines (fmap (("\t"++) . showCase) es)
showPrecT _ e = "(" ++ showPrecT 0 e ++ ")"

instance Show Term where
  show = showPrecT 0
