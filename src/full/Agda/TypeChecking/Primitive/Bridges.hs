{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE TypeFamilies #-}
{-|
Description : Primitive definitions (formation/computation). Inspired from `TypeChecking/Primitive/Cubical.hs`.

-}
module Agda.TypeChecking.Primitive.Bridges where

import Prelude hiding (null, (!!))

import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans ( lift )
import Control.Exception
import Data.Typeable
import Data.String

import Data.Either ( partitionEithers )
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable hiding (null)

import Agda.Interaction.Options ( optBridges )

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Monad

import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Lock

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Maybe

import Agda.Utils.Impossible
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Tuple
import Agda.Utils.Size
import qualified Agda.Utils.Pretty as P
import Agda.Utils.VarSet as VSet hiding (null)


-- * General todos
--   - see github issues for more severe issues
--   - should write unit tests
--   - there are TODO-antva's lying around
--   - pre bridges must be lock annoted? eg bridge form, intro. what matters is the internal lPi' vs nPi'
--     but could make that explicit in the Agda file declaring the primitive.
--   - sometimes rules in CH ask for apartedness (freshness) but no check is performed here
--   - bunch of unsettled questions in code below


-- * Prelude

-- | Generates error if --bridges pragma option was not set
requireBridges :: String -> TCM ()
requireBridges s = do
  bridges <- optBridges <$> pragmaOptions
  unless bridges $
    typeError $ GenericError $ "Missing option --bridges " ++ s

-- | Bridge interval as a type, i.e. as a term and a sort annotation
--   We use the LockUniv sort because bridge variables x : BI should be treated affinely
primBridgeIntervalType :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m) => m Type
primBridgeIntervalType = El LockUniv <$> primBridgeInterval

-- | two functions to fill implementations holes
dummyRedTerm0 :: ReduceM( Reduced MaybeReducedArgs Term)
dummyRedTerm0 = do
  return $ YesReduction NoSimplification $ Dummy "something" []

dummyRedTerm :: Term -> ReduceM( Reduced MaybeReducedArgs Term)
dummyRedTerm t = return $ YesReduction NoSimplification t


-- * extent primitive


-- | Type for extent primitive.
--   We use hoas style functions like hPi' to specifiy types in internal syntax.
--   primExtent : ∀ {ℓA ℓB} {A : BI → Set ℓA} {B : (x : BI) (a : A x) → Set ℓB}
--                (r : BI) (M : A r)                 should those r and M be there
--                (N0 : (a0 : A bi0) → B bi0 a0)
--                (N1 : (a1 : A bi1) → B bi1 a1)
--                (NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) →
--                      BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)) →
--                B r M
extentType :: TCM Type
extentType = do
  t <- runNamesT [] $
       hPi' "lA" (el $ cl primLevel) (\ lA ->
       hPi' "lB" (el $ cl primLevel) $ \ lB ->
       -- We want lines A B to use their bridge var affinely, hence the tick annotation lPi' vs nPi'
       hPi' "A"  (lPi' "x" primBridgeIntervalType $ \x -> (sort . tmSort <$> lA)) $ \ bA ->
       hPi' "B" (lPi' "x" primBridgeIntervalType $ \ x -> (el' lA (bA <@> x)) --> (sort . tmSort <$> lB) ) $ \bB ->
       nPi' "r" primBridgeIntervalType $ \ r ->
       nPi' "M" (el' lA (bA <@> r)) $ \bM ->
       nPi' "N0" (nPi' "a0" (el' lA (bA <@> cl primBIZero)) $ \a0 -> (el' lB (bB <@> cl primBIZero <@> a0))) $ \n0 ->
       nPi' "N1" (nPi' "a1" (el' lA (bA <@> cl primBIOne)) $ \a1 -> (el' lB (bB <@> cl primBIOne <@> a1))) $ \n1 ->
       nPi' "NN"
        (nPi' "a0" (el' lA (bA <@> cl primBIZero)) $ \a0 ->
         nPi' "a1" (el' lA (bA <@> cl primBIOne)) $ \a1 ->
         --todo make line argument bA implicit for primBridgeP? see Rules/Builtin.hs
         nPi' "aa" (el' lA $ cl primBridgeP <#> lA <@> bA <@> a0 <@> a1) $ \aa ->
         (el' lB $ cl primBridgeP <#> lB <@> newBline bB aa a0 a1 <@> (n0 <@> a0) <@> (n1 <@> a1)) ) $ \nn ->
       el' lB $ bB <@> r <@> bM )
  return t
  where
    newBline bB aa a0 a1 = lam "i" (\i -> bB <@> i <@> (aa <@@> (a0, a1, i) )) -- i is a bridge elim hence the double "at".


isTimeless' :: PureTCM m => Type -> m Bool
isTimeless' typ@(El stype ttyp) = do
  timeless <- mapM getName' timelessThings
  case ttyp of
    Def q _ | Just q `elem` timeless -> return True
    _                                -> return False


-- | @semiFreshForFvars fvs lk@ checks whether the following condition holds:
--   forall j in fvs, lk <=_time j -> timeless(j) where <=_time is left to right context order
semiFreshForFvars :: PureTCM m => VarSet -> Int -> m Bool
semiFreshForFvars fvs lki = do
  let lkLaters = filter (<= lki) (VSet.toList fvs) -- lk-laters, including lk itself and timeless vars
  timefullLkLaters <- flip filterM lkLaters $ \ j -> do
    tyj <- typeOfBV j --problem: can yield dummy type when it should not
    resj <- isTimeless' tyj
    return $ not resj
  reportSLn "tc.prim" 60 $ "semiFreshForFvars, timefullLkLaters: " ++ P.prettyShow timefullLkLaters
  return $ null timefullLkLaters

-- | Formation rule (extentType) and computation rule for the extent primitive.
--   For extent this include a boundary (BIZero, BIOne case) and beta rule.
--   the rules in CH sometimes require freshness but we lack those checks here
primExtent' :: TCM PrimitiveImpl
primExtent' = do
  requireBridges "in primExtent'"
  typ <- extentType
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 9 $ \extentArgs@[lA, lB, bA, bB,
                                                      r@(Arg rinfo rtm), bM,
                                                      n0@(Arg n0info n0tm), n1@(Arg n1info n1tm),
                                                      nn@(Arg nninfo nntm)] -> do
    --goal ReduceM(Reduced MaybeReducedArgs Term)
    viewr <- bridgeIntervalView rtm --should reduceB because of metas
    case viewr of
      BIZero ->  redReturn $ n0tm `apply` [bM] -- YesReduction, YesSimplification
      BIOne ->   redReturn $ n1tm `apply` [bM]
      -- QST: no need to check that #occ of r in M <= 1 because this will be checked later?
      -- in order to reduce extent_r(M ; ..) we need to check that M has no timefull r-laters
      BOTerm rtm@(Var ri []) -> do
        bM' <- reduceB' bM --because some timefull r-laters may disappear
        let bMtm' = unArg $ ignoreBlocking $ bM'
        let fvM0 = freeVarsIgnore IgnoreNot $ bMtm' -- correct ignore flag?
        -- let rigidFvM = rigidVars fvM0
        -- let flexFvM = flexibleVars fvM0 --free vars appearing under a meta
        let fvM = allVars fvM0
        shouldRedExtent <- semiFreshForFvars fvM ri
        case shouldRedExtent of
          False -> do
            reportSLn "tc.prim.extent" 30 $ P.prettyShow rtm ++ " not semifresh for " ++ P.prettyShow bMtm'
            reportSLn "tc.prim.extent" 30 $ "because fvs are " ++ P.prettyShow fvM
            fallback lA lB bA bB r bM' n0 n1 nn --should throw error?
          True -> do
            reportSLn "tc.prim.extent" 30 $ P.prettyShow rtm ++ " is semifresh for " ++ P.prettyShow bMtm'
            bi0 <- getTerm "primExtent" builtinBIZero
            bi1 <- getTerm "primExtent" builtinBIOne
            let lamM = captureIn bMtm' ri   -- λ r. M
            reportSLn "tc.prim.extent" 30 $ "captureIn (( " ++ P.prettyShow bMtm' ++" )) (( " ++ P.prettyShow ri ++ " ))"
            reportSLn "tc.prim.extent" 30 $ "captureIn ((M)) ((r)) is " ++ P.prettyShow lamM
            redReturn $ nntm `applyE` [Apply $ argN $ lamM `apply` [argN bi0],
                                   Apply $ argN $ lamM `apply` [argN bi1],
                                   Apply $ argN $ lamM,
                                   IApply n0tm n1tm rtm  ]
      _ -> __IMPOSSIBLE__ --beware of metas?
  where
    -- | captures r in M, ie returns λ r. M. This is sound thanks to the fv-analysis.
    --  Γ0 , r:BI , Γ1, r''   --σ-->   Γ0 , r:BI , Γ1 ⊢ M   where    r[σ] = r''
    -- idea: sigma is a stack of :# (see Substitution'). leaves of sigma:
    -- Γ0, r:BI , Γ1, r'' ⊢ r''        Γ0, r:BI , Γ1, r'' ⊢ Γ0
    -- --------------------------------------------------------
    -- Γ0, r:BI , Γ1, r'' ⊢ Γ0, r    where r mapsto r''
    captureIn m ri =
      let sigma = ([var (i+1) | i <- [0 .. ri - 1] ] ++ [var 0]) ++# raiseS (ri + 2) in
      Lam ldArgInfo $ Abs "r" $ applySubst sigma m
    ldArgInfo = setLock IsLock defaultArgInfo
    fallback lA lB bA bB r bM' n0 n1 nn =
      return $ NoReduction $ map notReduced [lA, lB, bA, bB, r] ++
                                   [reduced bM'] ++ map notReduced [n0, n1, nn]


-- * Gel type primitives: Gel, gel, ungel
--   We take inspiration from the cubical Glue types and primitives.
--   In their case, the type, the intro and elim primitives are really agda primitives.
--   the boundary rules are part of the various PrimitiveImpl.
--   the Glue beta rule is part of the unglue PrimitiveImpl
--   the Glue eta rule is specified elsewhere


-- | Gel : ∀ {ℓA ℓ} (r : BI) (A0 : Set ℓA) (A1 : Set ℓA) (R : A0 → A1 → Set ℓ) → Set ℓ
-- TODO-antva: should I check that A0 A1 R are apart from r?
-- the return type is really Set ℓ?
gelType :: TCM Type
gelType = do
  t <- runNamesT [] $
       hPi' "lA" (el primLevel) $ \lA ->
       hPi' "lR" (el primLevel) $ \lR ->
       lPi' "r" primBridgeIntervalType $ \r ->
       nPi' "A0" (sort . tmSort <$> lA) $ \bA0 ->
       nPi' "A1" (sort . tmSort <$> lA) $ \bA1 ->
       nPi' "R" ( (el' lA bA0) --> (el' lA bA1) --> (sort . tmSort <$> lR) ) $ \bR ->
       sort . tmSort <$> lR
  return t


-- | Formation rule for Gel type + boundary rule
--   should I perform a fv analysis? if yes when should I do it??
primGel' :: TCM PrimitiveImpl
primGel' = do
  requireBridges "in primGel'"
  typ <- gelType
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 6 $ \gelTypeArgs@[lA, lR, r@(Arg rinfo rtm), bA0@(Arg ainfo0 bA0tm),
                                                                   bA1@(Arg ainfo1 bA1tm), bR]-> do
    --goal ReduceM(Reduced MaybeReducedArgs Term)
    viewr <- bridgeIntervalView rtm --should reduceB because of metas
    case viewr of
      BIZero -> redReturn bA0tm
      BIOne -> redReturn bA1tm
      BOTerm rtm@(Var ri []) -> return $ NoReduction $ map notReduced gelTypeArgs
      _ -> __IMPOSSIBLE__ --metas...

-- | prim^gel : ∀ {ℓA ℓ} {A0 A1 : Set ℓA} {R : A0 → A1 → Set ℓ}
--              (r : BI) (M0 : A0) (M1 : A1) (P : R M0 M1) →
--              Gel r A0 A1 R
-- should check freshness? cf ch rules
prim_gelType :: TCM Type
prim_gelType = do
  t <- runNamesT [] $
       hPi' "lA" (el primLevel) $ \lA ->
       hPi' "l" (el primLevel) $ \l ->
       hPi' "A0" (sort . tmSort <$> lA) $ \bA0 ->
       hPi' "A1" (sort . tmSort <$> lA) $ \bA1 ->
       hPi' "R" ( (el' lA bA0) --> (el' lA bA1) --> (sort . tmSort <$> l) ) $ \bR ->
       nPi' "r" primBridgeIntervalType $ \r ->  --lock?
       nPi' "M0" (el' lA bA0) $ \bM0 ->
       nPi' "M1" (el' lA bA1) $ \bM1 ->
       nPi' "P" (el' l $ bR <@> bM0 <@> bM1) $ \bP ->
       el' l $ cl primGel <#> lA <#> l <@> r <@> bA0 <@> bA1 <@> bR
  return t
  

-- -- | introduction term for Gel is gel (sometimes also called prim_gel / prim_gel' / prim^gel)
prim_gel' :: TCM PrimitiveImpl
prim_gel' = do
  requireBridges "in prim_gel'"
  typ <- prim_gelType
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 9 $ \gelArgs@[lA, l, bA0, bA1,
                                                               bR, r@(Arg rinfo rtm),
                                                               bM0@(Arg _ bM0tm), bM1@(Arg _ bM1tm), bP]-> do
    --goal ReduceM(Reduced MaybeReducedArgs Term)
    viewr <- bridgeIntervalView rtm --should reduceB because of metas
    case viewr of
      BIZero -> redReturn bM0tm
      BIOne -> redReturn bM1tm
      BOTerm rtm@(Var ri []) -> return $ NoReduction $ map notReduced gelArgs
      _ -> __IMPOSSIBLE__ --metas...  
