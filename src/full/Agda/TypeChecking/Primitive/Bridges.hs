{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE TypeFamilies #-}
{-|
Description : Auxiliary functions for internal syntax bridges. Inspired from `TypeChecking/Primitive/Cubical.hs`.

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


-- | Generates error if --bridges pragma option was not set
-- Used when typechecking the bridge interval
requireBridges :: String -> TCM ()
requireBridges s = do
  bridges <- optBridges <$> pragmaOptions
  unless bridges $
    typeError $ GenericError $ "Missing option --bridges " ++ s

-- | Types are terms with a sort annotation.
-- Here we turn the bridge interval (informally: BI) into such a type by specifying a sort for it.
-- This sort is LockUniv. The intent is that bridge variables x : BI should be treated affinely,
-- as it is the case for tick variables.
primBridgeIntervalType :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m) => m Type
primBridgeIntervalType = El LockUniv <$> primBridgeInterval



-- | type for extent primitive.
-- We use hoas style functions like hPi' to specifiy types in internal syntax.
-- primExtent : ∀ {ℓA ℓB} {A : BI → Set ℓA} {B : (x : BI) (a : A x) → Set ℓB}
--              (r : BI) (M : A r)
--              (N0 : (a0 : A bi0) → B bi0 a0)
--              (N1 : (a1 : A bi1) → B bi1 a1)
--              (NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)) →
--              BridgeP (λ x → (a : A x) → B x a) N0 N1
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
       -- findLevel lA lB = level of this pi-type: @newABline(i) := (a:A i) -> B i a@
       -- given that A i : Set lA and B i a : Set lB ...
       el' (findLevel lA lB) $ cl primBridgeP <#> (findLevel lA lB) <@> newABline lA lB bA bB <@> n0 <@> n1 )
  return t
  where
    newBline bB aa a0 a1 = lam "i" (\i -> bB <@> i <@> (aa <@@> (a0, a1, i) )) -- i is a bridge elim hence the double "at".
    newABline lA lB bA bB = lam "i"  $ \i -> do
      typ <- nPi' "ai" (el' lA $ bA <@> i) $ \ai -> el' lB $ bB <@> i <@> ai
      return $ unEl typ
    -- | @findLevel lA lB :: m Term@ for relevant m. lA lB are effectful as well.
    -- computes the supremum of the Level-Term's lA lB and yields a term.
    findLevel lA lB = do
      tlA <- lA
      tlB <- lB -- :: Term
      case (tlA, tlB) of
        (Level llA, Level llB) -> return $ levelTm $ levelLub llA llB
        (_ , _) -> typeError $ GenericError "Level sup for things that are not levels in extentType"

-- | two functions to fill implementations holes
dummyRedTerm0 :: ReduceM( Reduced MaybeReducedArgs Term)
dummyRedTerm0 = do
  return $ YesReduction NoSimplification $ Dummy "something" []

dummyRedTerm :: Term -> ReduceM( Reduced MaybeReducedArgs Term)
dummyRedTerm t = return $ YesReduction NoSimplification t


-- | Formation rule (extentType) and computation rule for the extent primitive.
-- For extent this include a boundary (BIZero, BIOne case) and beta rule.
primExtent' :: TCM PrimitiveImpl
primExtent' = do
  requireBridges "in primExtent'"
  typ <- extentType
  return $ PrimImpl typ $ primFun __IMPOSSIBLE__ 9 $ \extentArgs@[lA, lB, bA, bB,
                                                      r@(Arg rinfo rtm), bM@(Arg bMinfo bMtm),
                                                      n0@(Arg n0info n0tm), n1@(Arg n1info n1tm),
                                                      nn@(Arg nninfo nntm)] -> do --TODO: non exh pattern match?
    --goal ReduceM(Reduced MaybeReducedArgs Term)
    viewr <- bridgeIntervalView rtm --should I reduce r?
    case viewr of
      BIZero ->  redReturn $ n0tm `apply` [bM] -- YesReduction/YesSimplification in redReturn:
      BIOne ->   redReturn $ n1tm `apply` [bM] -- the head @extent@ disappeared/reduction leads to a simpler term
      -- todo: fv analysis in M for rv? condition: the free vars of M should not be later-r's
      -- if needed I could ask whether lamM : (@tick r : BI) -> A r. Andrea: bad idea
      -- also: not sure all the cases are treated correctly (what about metas)
      BOTerm rv@(Var ri []) -> do
        bi0 <- getTerm "primExtent" builtinBIZero --first arg to spec location
        bi1 <- getTerm "primExtent" builtinBIOne
        redReturn $ nntm `applyE` [Apply $ argN $ (lamM bMtm) `apply` [argN bi0],
                                   Apply $ argN $ (lamM bMtm) `apply` [argN bi1],
                                   Apply $ argN $ lamM bMtm,
                                   IApply (n0tm, n1tm, rtm)  ]
      _ -> __IMPOSSIBLE__
  where
    lamM bMtm = ( Lam ldArgInfo $ Abs "r" bMtm ) -- Lam ArgInfo (Abs Term)
    ldArgInfo = setLock IsLock defaultArgInfo
                                         
-- prim_glue' :: TCM PrimitiveImpl
-- prim_glue' = do
--   requireCubical CFull ""
--   t <- runNamesT [] $
--        hPi' "la" (el $ cl primLevel) (\ la ->
--        hPi' "lb" (el $ cl primLevel) $ \ lb ->
--        hPi' "A" (sort . tmSort <$> la) $ \ a ->
--        hPi' "φ" primIntervalType $ \ φ ->
--        hPi' "T" (pPi' "o" φ $ \ o ->  el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
--        hPi' "e" (pPi' "o" φ $ \ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primEquiv <#> lb <#> la <@> (t <@> o) <@> a) $ \ e ->
--        pPi' "o" φ (\ o -> el' lb (t <@> o)) --> (el' la a --> el' lb (cl primGlue <#> la <#> lb <@> a <#> φ <@> t <@> e)))
--   view <- intervalView'
--   one <- primItIsOne
--   return $ PrimImpl t $ primFun __IMPOSSIBLE__ 8 $ \ts ->
--     case ts of
--       [la,lb,bA,phi,bT,e,t,a] -> do
--        sphi <- reduceB' phi
--        case view $ unArg $ ignoreBlocking $ sphi of
--          IOne -> redReturn $ unArg t `apply` [argN one]
--          _    -> return (NoReduction $ map notReduced [la,lb,bA] ++ [reduced sphi] ++ map notReduced [bT,e,t,a])
--       _ -> __IMPOSSIBLE__
