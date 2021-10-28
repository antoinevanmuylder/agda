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


-- | Generates error if --bridges pragma option was not set
requireBridges :: String -> TCM ()
requireBridges s = do
  bridges <- optBridges <$> pragmaOptions
  unless bridges $
    typeError $ GenericError $ "Missing option --bridges " ++ s

-- | Bridge interval as a type, i.e. as a term and a sort annotation
--   We use the LockUniv sort because bridge variables x : BI should be treated affinely,
primBridgeIntervalType :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m) => m Type
primBridgeIntervalType = El LockUniv <$> primBridgeInterval



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
       -- el' (lA `levelLubTmM` lB) $ cl primBridgeP <#> (lA `levelLubTmM` lB) <@> newABline lA lB bA bB <@> n0 <@> n1 )
  return t
  where
    newBline bB aa a0 a1 = lam "i" (\i -> bB <@> i <@> (aa <@@> (a0, a1, i) )) -- i is a bridge elim hence the double "at".
    -- -- use level of this pi-type: @newABline(i) := (a:A i) -> B i a@  ?
    -- newABline lA lB bA bB = lam "i"  $ \i -> do
    --   typ <- nPi' "ai" (el' lA $ bA <@> i) $ \ai -> el' lB $ bB <@> i <@> ai
    --   return $ unEl typ

-- | two functions to fill implementations holes
dummyRedTerm0 :: ReduceM( Reduced MaybeReducedArgs Term)
dummyRedTerm0 = do
  return $ YesReduction NoSimplification $ Dummy "something" []

dummyRedTerm :: Term -> ReduceM( Reduced MaybeReducedArgs Term)
dummyRedTerm t = return $ YesReduction NoSimplification t


isTimeless' :: PureTCM m => Type -> m Bool
isTimeless' typ@(El stype ttyp) = do
  timeless <- mapM getName' timelessThings
  case ttyp of
    Def q _ | Just q `elem` timeless -> return True
    _                                -> return False

-- | @semiFreshForFvars fvs lk@ checks whether the following condition holds:
--   forall j in fvs, lk <=_time j -> timeless(j) where <=_time is left to right context order
--   precond: lk is a variable (no elims)
semiFreshForFvars :: PureTCM m => VarSet -> Term -> m Bool
semiFreshForFvars fvs lk@(Var i []) = do
  let lkLaters = filter (<= i) (VSet.toList fvs) -- lk-laters, including lk itself and timeless vars
  timefullLkLaters <- flip filterM lkLaters $ \ j -> do
    tyj <- typeOfBV j
    resj <- isTimeless' tyj
    return $ not resj
  return $ null timefullLkLaters
semiFreshForFvars fvs _ = __IMPOSSIBLE__

-- | Formation rule (extentType) and computation rule for the extent primitive.
--   For extent this include a boundary (BIZero, BIOne case) and beta rule.
primExtent' :: TCM PrimitiveImpl
primExtent' = do
  requireBridges "in primExtent'"
  typ <- extentType
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 9 $ \extentArgs@[lA, lB, bA, bB,
                                                      r@(Arg rinfo rtm), bM,
                                                      n0@(Arg n0info n0tm), n1@(Arg n1info n1tm),
                                                      nn@(Arg nninfo nntm)] -> do --TODO: non exh pattern match?
    --goal ReduceM(Reduced MaybeReducedArgs Term)
    viewr <- bridgeIntervalView rtm
    case viewr of
      BIZero ->  redReturn $ n0tm `apply` [bM] -- YesReduction, YesSimplification
      BIOne ->   redReturn $ n1tm `apply` [bM]
      -- TODO: fv analysis in M for rv? condition: forall v in fv(M), r <=_time v -> timeless(v)
      -- QST: no need to check that #occ of r in M <= 1 because this will be checked later?
      -- QST: once a term is converted is it typechecked again
      -- TODO: not sure all the cases are treated correctly (what about metas).
      BOTerm rtm@(Var ri []) -> do
        bM' <- reduceB' bM
        case bM' of
          Blocked{} -> fallback lA lB bA bB r bM' n0 n1 nn
          NotBlocked{} -> do -- means no metas at all?
            let bMtm' = unArg $ ignoreBlocking $ bM'
            let fvM0 = freeVarsIgnore IgnoreNot $ bMtm' -- correct ignore flag?
            let fvM = allVars fvM0
            -- flex = flexibleVars fvM0 --free vars appearing under a meta
            shouldRedExtent <- semiFreshForFvars fvM rtm -- andM [return $ null flex, semiFreshForFvars fvM rtm] extent_r ( M ; ...)
            case shouldRedExtent of
              False -> traceDebugMessage "tc.prim" 20 "not semifresh" $
                fallback lA lB bA bB r bM' n0 n1 nn --should throw error?
              True -> traceDebugMessage "tc.prim" 20 "is semifresh" $ do
                bi0 <- getTerm "primExtent" builtinBIZero --use getBuiltinThing instead?
                bi1 <- getTerm "primExtent" builtinBIOne
                redReturn $ nntm `applyE` [Apply $ argN $ (lamM bMtm') `apply` [argN bi0],
                                       Apply $ argN $ (lamM bMtm') `apply` [argN bi1],
                                       Apply $ argN $ lamM  $ bMtm',
                                       IApply n0tm n1tm rtm  ]
      _ -> __IMPOSSIBLE__
  where
    -- QST: how do we know that "r" is bound in M though --> de bruijn
    -- for capturing I want m to be in context @gamma\r, r |- m : Ar@
    -- Monad/Context.hs seems to be the relevant file, together with the @instance MonadAddContext ReduceM@
    -- there is also the @instance MonadTCEnv ReduceM@ and the localTC method that could be interesting
    lamM m = ( Lam ldArgInfo $ Abs "r" m )
    -- captureIn m r@(Var ri []) =      
    ldArgInfo = setLock IsLock defaultArgInfo
    fallback lA lB bA bB r bM' n0 n1 nn =
      return $ NoReduction $ map notReduced [lA, lB, bA, bB, r] ++
                                   [reduced bM'] ++ map notReduced [n0, n1, nn]


