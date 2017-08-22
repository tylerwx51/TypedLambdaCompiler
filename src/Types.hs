module Types where

import Data.List as List hiding(lookup)
import Data.Monoid hiding(Sum)

{-
Types for Core
-}
data MonoType = TVar String
              | TCon String
              | TApp MonoType MonoType

tApp :: MonoType -> [MonoType] -> MonoType
tApp applier [] = applier
tApp applier [t] = TApp applier t
tApp applier (t:ts) = tApp (TApp applier t) ts

arrowType :: MonoType
arrowType = TCon "Arrow" --(KArrow KType (KArrow KType KType))

sumType :: MonoType
sumType = TCon "Sum" --(KArrow KType (KArrow KType KType))

productType :: MonoType
productType = TCon "Prod" --(KArrow KType (KArrow KType KType))

arrow :: MonoType -> MonoType -> MonoType
arrow t1 t2 = tApp arrowType [t1, t2]

sumT :: MonoType -> MonoType -> MonoType
sumT t1 t2 = tApp sumType [t1, t2]

prod :: MonoType -> MonoType -> MonoType
prod t1 t2 = tApp productType [t1, t2]

unit :: MonoType
unit = TCon "Unit" --KType

void :: MonoType
void = TCon "Void" --KType

fixT :: MonoType -> MonoType
fixT = TApp (TCon "Fix")

showPrec :: Int -> MonoType -> String
showPrec _ (TVar str) = str
showPrec _ (TCon str) = str
showPrec _ (TApp t1 t2) = "(" ++ showPrec 0 t1 ++ " " ++ showPrec 1 t2 ++ ")"

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

{-
Substitions used in type-checking
-}
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
  substitute n t (TApp t1 t2) = TApp (substitute n t t1) (substitute n t t2)
  substitute _ _ t = t

  freeTypeVars (TVar str) = [str]
  freeTypeVars (TApp t1 t2) = freeTypeVars t1 ++ freeTypeVars t2
  freeTypeVars _ = []

instance Substitable PolyType where
  substitute n t (T m) = T $ substitute n t m
  substitute n t (Forall a p)
    | n == a = Forall a p
    | otherwise = Forall a (substitute n t p)

  freeTypeVars (T mType) = freeTypeVars mType
  freeTypeVars (Forall a pType) = List.delete a (freeTypeVars pType)

{-
Patterns that can be used in case blocks
-}
data Pattern = MatchLeft Pattern
             | MatchRight Pattern
             | MatchProd Pattern Pattern
             | MatchUnit
             | MatchFix Pattern
             | Otherwise String

instance Show Pattern where
  show (MatchLeft patt) = "Left (" ++ show patt ++ ")"
  show (MatchRight patt) = "Right (" ++ show patt ++ ")"
  show (MatchProd patt1 patt2) = "(" ++ show patt1 ++ ", " ++ show patt2 ++ ")"
  show (MatchFix patt) = "Fix (" ++ show patt ++ ")"
  show (Otherwise x) = x
  show MatchUnit = "()"

varList :: Pattern -> [String]
varList (MatchLeft patt) = varList patt
varList (MatchRight patt) = varList patt
varList (MatchProd patt1 patt2) = varList patt1 ++ varList patt2
varList (MatchFix patt) = varList patt
varList (Otherwise t) = [t]
varList MatchUnit = []


{- Raw Terms -}
data Literal = LitInt Int | LitDouble Double

data Term = Apply Term Term
          | Let String Term Term
          | Lambda String Term
          | Case [(Pattern, Term)]
          | Var String
          | Coerce Term MonoType
          | Lit Literal

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
showPrecT 0 (Coerce term ty) = show term ++ " : " ++ show ty
showPrecT _ e = "(" ++ showPrecT 0 e ++ ")"

instance Show Term where
  show = showPrecT 0
