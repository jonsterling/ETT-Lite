{- PiForall language, OPLSS, Summer 2013 -}

{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | Compare two terms for equality
module Equal (whnf,equate,ensureType,ensurePi, ensureTyEq,  ensureTCon  ) where

import Syntax
import Environment

import Unbound.LocallyNameless hiding (Data, Refl)
import Control.Monad.Error (catchError)
import Control.Applicative ((<$>))
import Control.Monad
import Data.List

(<|>) :: TcMonad a -> TcMonad a -> TcMonad a
x <|> y = catchError x (const y)

getEquations :: [Decl] -> [(Term, Term)]
getEquations (Sig _ (TyEq x y) : gamma) = (x,y) : getEquations gamma
getEquations (_ : gamma) = getEquations gamma
getEquations [] = []

termsEqualTo :: [(Term, Term)] -> Term -> TcMonad [Term]
termsEqualTo ((a,b) : es) x = do
  eqns <- (equate' False a x >> return [a,b]) `catchError` \_ ->
    (equate' False b x >> return [a,b]) `catchError` \_ ->
      return []
  rest <- termsEqualTo es x
  return $ eqns ++ rest
termsEqualTo _ x = return []

combinations :: [a] -> [a] -> [(a,a)]
combinations xs ys = foldr (\x m -> map (x,) ys ++ m) [] xs

findEquation :: [(Term, Term)] -> Term -> Term -> TcMonad ()
findEquation es x y = do
  xeqs <- termsEqualTo es x
  yeqs <- termsEqualTo es y
  let combos = combinations xeqs yeqs
  matches <- flip filterM combos $ \(a,b) ->
    (equate' False a b >> return True) `catchError` \_ ->
      return False

  case matches of
    [] -> err [DS "No equation for ", DD x, DS "=", DD y, DS "in context"]
    _ -> return ()


eqReflect :: [Decl] -> Term -> Term -> TcMonad ()
eqReflect g x y = findEquation (getEquations g) x y

equate :: Term -> Term -> TcMonad ()
equate = equate' True

-- | compare two expressions for equality
-- ignores type annotations during comparison
-- throws an error if the two types cannot be matched up
equate' :: Bool -> Term -> Term -> TcMonad ()
equate' shouldReflect t1 t2 = let recurse = equate' shouldReflect in do
  n1 <- whnf t1
  n2 <- whnf t2

  case (n1, n2) of
    (Var x,  Var y)  | x == y -> return ()
    (Lam bnd1, Lam bnd2) -> do
      Just (x, b1, _, b2) <- unbind2 bnd1 bnd2
      recurse b1 b2
    (v, Lam bnd) -> do
      (x, b) <- unbind bnd
      case b of
        App f (Arg x') -> recurse f v
        _ -> err [DS "Couldn't apply eta rule"]
    (App a1 a2, App b1 b2) -> do
      recurse a1 b1
      equateArgs a2 b2
    (Type i, Type j) | i == j -> return ()
    (Pi bnd1, Pi bnd2) -> do
      Just ((x, unembed -> tyA1), tyB1,
            (_, unembed -> tyA2), tyB2) <- unbind2 bnd1 bnd2
      recurse tyA1 tyA2
      recurse tyB1 tyB2

    (Ann at1 _, at2) -> recurse at1 at2
    (at1, Ann at2 _) -> recurse at1 at2
    (Paren at1, at2) -> recurse at1 at2
    (at1, Paren at2) -> recurse at1 at2
    (Pos _ at1, at2) -> recurse at1 at2
    (at1, Pos _ at2) -> recurse at1 at2

    (TrustMe _, TrustMe _) ->  return ()

    (TyUnit, TyUnit)   -> return ()
    (LitUnit, LitUnit) -> return ()

    (TyBool, TyBool)   -> return ()

    (LitBool b1, LitBool b2) | b1 == b2 -> return ()

    (If a1 b1 c1 _, If a2 b2 c2 _) ->
      recurse a1 a2 >> recurse b1 b2 >> recurse c1 c2

    (Let bnd1, Let bnd2) -> do
      Just ((x,unembed -> rhs1), body1,
            (_,unembed -> rhs2), body2) <- unbind2 bnd1 bnd2
      recurse rhs1 rhs2
      recurse body1 body2

    (Sigma bnd1, Sigma bnd2) -> do
      Just ((x, unembed -> tyA1), tyB1,
            (_, unembed -> tyA2), tyB2) <- unbind2 bnd1 bnd2
      recurse tyA1 tyA2
      recurse tyB1 tyB2

    (Prod a1 b1 _, Prod a2 b2 _) -> do
      recurse a1 a2
      recurse b1 b2

    (Pcase s1 bnd1 _, Pcase s2 bnd2 _) -> do
      recurse s1 s2
      Just ((x,y), body1, _, body2) <- unbind2 bnd1 bnd2
      recurse body1 body2

    (TyEq a b, TyEq c d) -> recurse a c >> recurse b d

    (Refl _,  Refl _) -> return ()

    (Subst at1 _ _, at2) -> recurse at1 at2

    (at1, Subst at2 _ _) -> recurse at1 at2

    (Contra a1 _, Contra a2 _) -> return ()


    (TCon c1 ts1, TCon c2 ts2) | c1 == c2 ->
      zipWithM_ recurse ts1 ts2
    (DCon d1 a1 _, DCon d2 a2 _) | d1 == d2 ->
      zipWithM_ equateArgs a1 a2
    (Case s1 brs1 ann1, Case s2 brs2 ann2)
      | length brs1 == length brs2 -> do
      recurse s1 s2
      -- require branches to be in the same order
      -- on both expressions
      let matchBr (Match bnd1) (Match bnd2) = do
            mpb <- unbind2 bnd1 bnd2
            case mpb of
              Just (p1, a1, p2, a2) | p1 == p2 -> do
                recurse a1 a2
              _ -> err [DS "Cannot match branches in",
                              DD n1, DS "and", DD n2]
      zipWithM_ matchBr brs1 brs2

    (Smaller a b, Smaller c d) ->
      recurse a c >> recurse b d

    (Ind bnd1 ann1, Ind bnd2 ann2) -> do
      Just ((f,x), b1, _, b2) <- unbind2 bnd1 bnd2
      recurse b1 b1

    (PiC bnd1, PiC bnd2) -> do
      Just ((x, unembed -> tyA1), (c1, tyB1),
            (_, unembed -> tyA2), (c2, tyB2)) <- unbind2 bnd1 bnd2
      recurse tyA1 tyA2
      recurse c1 c2
      recurse tyB1 tyB2

    (_,_) -> do
      gamma <- getLocalCtx
      if shouldReflect
        then eqReflect gamma n1 n2
        else err [DS "Expected", DD t2, DS "which normalizes to", DD n2,
                  DS "but found", DD t1,  DS "which normalizes to", DD n1,
                  DS "in context:", DD gamma]

equateArgs :: Arg -> Arg -> TcMonad ()
equateArgs (Arg t1) (Arg t2) = equate t1 t2

-------------------------------------------------------

-- | Ensure that the given type 'ty' is some 'Type i' for
-- some i
ensureType :: Term -> TcMonad Int
ensureType ty = do
  nf <- whnf ty
  case nf of
    Type i -> return i
    _  -> err [DS "Expected a Type i, instead found", DD nf]

-- | Ensure that the given type 'ty' is some sort of 'Pi' type
-- (or could be normalized to be such) and return the components of
-- the type.
-- Throws an error if this is not the case.
ensurePi :: Term -> TcMonad (TName, Term, Term, Maybe Term)
ensurePi ty = do
  nf <- whnf ty
  case nf of
    (Pi bnd) -> do
      ((x, unembed -> tyA), tyB) <- unbind bnd
      return (x, tyA, tyB, Nothing)
    (PiC bnd) -> do
      ((x, unembed -> tyA), (constr, tyB)) <- unbind bnd
      return (x, tyA, tyB, Just constr)
    _ -> err [DS "Expected a function type, instead found", DD nf]


-- | Ensure that the given 'ty' is an equality type
-- (or could be normalized to be such) and return
-- the LHS and RHS of that equality
-- Throws an error if this is not the case.
ensureTyEq :: Term -> TcMonad (Term,Term)
ensureTyEq ty = do
  nf <- whnf ty
  case nf of
    TyEq m n -> return (m, n)
    _ -> err [DS "Expected an equality type, instead found", DD nf]


-- | Ensure that the given type 'ty' is some tycon applied to
--  params (or could be normalized to be such).
-- Throws an error if this is not the case.
ensureTCon :: Term -> TcMonad (TCName, [Term])
ensureTCon aty = do
  nf <- whnf aty
  case nf of
    (TCon n params) -> return (n, params)
    _ -> err [DS "Expected a data type",
              DS ", but found", DD nf]



-------------------------------------------------------
-- | Convert a term to its weak-head normal form.
-- If there is a variable in the active position with
-- a definition in the context, expand it.
whnf :: Term -> TcMonad Term

whnf (Var x) = do
  maybeDef <- lookupDef x
  case (maybeDef) of
    (Just d) -> whnf d
    _ -> return (Var x)

whnf (App t1 arg@(Arg t2)) = do
  nf <- whnf t1
  case nf of
    (Lam bnd) -> do
      ((x,_),body) <- unbind bnd
      whnf (subst x t2 body)
        -- only unfold applications of inductive definitions
    -- if the argument is a data constructor.
    (Ind bnd _) -> do
      nf2 <- whnf t2
      case nf2 of
        (DCon _ _ _) -> do
          ((f,x),body) <- unbind bnd
          whnf (subst x nf2 (subst f nf body))
        _ -> return (App nf arg)

    _ -> do
      return (App nf arg)



whnf (If t1 t2 t3 ann) = do
  nf <- whnf t1
  case nf of
    (LitBool b) -> if b then whnf t2 else whnf t3
    _ -> return (If nf t2 t3 ann)

whnf (Pcase a bnd ann) = do
  nf <- whnf a
  case nf of
    Prod b c _ -> do
      ((x,y), body) <- unbind bnd
      whnf (subst x b (subst y c body))
    _ -> return (Pcase nf bnd ann)


whnf t@(Ann tm ty) =
  err [DS "Unexpected arg to whnf:", DD t]
whnf t@(Paren x)   =
  err [DS "Unexpected arg to whnf:", DD t]
whnf t@(Pos _ x)   =
  err [DS "Unexpected position arg to whnf:", DD t]

whnf (Let bnd)  = do
  ((x,unembed->rhs),body) <- unbind bnd
  whnf (subst x rhs body)


whnf (Subst tm pf annot) = do
  pf' <- whnf pf
  case pf' of
    Refl _ -> whnf tm
    _ -> return (Subst tm pf' annot)


whnf (Case scrut mtchs annot) = do
  nf <- whnf scrut
  case nf of
    (DCon d args _) -> f mtchs where
      f (Match bnd : alts) = (do
          (pat, br) <- unbind bnd
          ss <- patternMatches (Arg nf) pat
          whnf (substs ss br))
            `catchError` \ _ -> f alts
      f [] = err $ [DS "Internal error: couldn't find a matching",
                    DS "branch for", DD nf, DS "in"] ++ (map DD mtchs)
    _ -> return (Case nf mtchs annot)



-- all other terms are already in WHNF
whnf tm = return tm


-- | Determine whether the pattern matches the argument
-- If so return the appropriate substitution
patternMatches :: Arg -> Pattern -> TcMonad [(TName, Term)]
patternMatches (Arg t) (PatVar x) = return [(x, t)]
patternMatches (Arg t) pat@(PatCon d' pats) = do
  nf <- whnf t
  case nf of
    (DCon d args _) | d == d' ->
       concat <$> zipWithM patternMatches args pats
    _ -> err [DS "arg", DD nf, DS "doesn't match pattern", DD pat]


