module Eval where

import Control.Applicative
import Types

data Evaled = L [(String, Evaled)] String Term
            | ECon String [Evaled]
            | EInt Int
            | EDouble Double
            | ECase [(String, Evaled)] [(Pattern, Term)]
            | ERec [(String, Evaled)] Term
            deriving(Show)

patternBreakDown :: Pattern -> Evaled -> Maybe [(String, Evaled)]
patternBreakDown (MatchLeft patt) (ECon "Left" [arg]) = patternBreakDown patt arg
patternBreakDown (MatchRight patt) (ECon "Right" [arg]) = patternBreakDown patt arg
patternBreakDown (MatchProd patt1 patt2) (ECon "MkPair" [arg1, arg2]) =
  liftA2 (++) (patternBreakDown patt1 arg1) (patternBreakDown patt2 arg2)
patternBreakDown MatchUnit (ECon "Unit" []) = Just []
patternBreakDown (MatchFix patt) (ECon "MkFix" [arg]) = patternBreakDown patt arg
patternBreakDown (Otherwise str) value = Just [(str, value)]
patternBreakDown _ _ = Nothing

caseApply :: [(String, Evaled)] -> [(Pattern, Term)] -> Evaled -> Evaled
caseApply _ [] _ = error "Void can't be constructed"
caseApply env ((p, e) : ts) value =
  case patternBreakDown p value of
    Nothing -> caseApply env ts value
    Just env' -> evalTerm (env ++ env') e

lamApply :: [(String, Evaled)] -> String -> Term -> Evaled -> Evaled
lamApply env var e value = evalTerm ((var, value) : env) e

evalTerm :: [(String, Evaled)] -> Term -> Evaled
evalTerm env (Apply e1 e2) =
  let fValue = evalTerm env e1
      xValue = evalTerm env e2
  in case fValue of
      (L inEnv var e) -> lamApply inEnv var e xValue
      (ECon con args) -> ECon con (args ++ [xValue])
      (ECase inEnv partials) -> caseApply inEnv partials xValue
      _ -> undefined
evalTerm env (Let vars e) = let newEnvs = fmap (\(var, e1) -> (var, ERec inEnv e1)) vars
                                inEnv = newEnvs ++ env
                                vs = fmap (\(var, e1) -> (var, evalTerm inEnv e1)) vars
                            in evalTerm (vs ++ env) e
evalTerm env (Lambda var e) = L env var e
evalTerm env (Case ps) = ECase env ps
evalTerm env (Var str) =
  case lookup str env of
    Just (ERec inEnv e) -> evalTerm inEnv e
    Just value -> value
    Nothing -> error $ "Can't find " ++ str
evalTerm _ (Lit (LitInt num)) = EInt num
evalTerm _ (Lit (LitDouble num)) = EDouble num
evalTerm env (Coerce e _) = evalTerm env e
