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
-- We use the hoas style functions like hPi' (hidden pi) to specifiy types in internal syntax.
-- primExtent : ∀ {ℓA ℓB} {A : BI → Set ℓA} {B : (x : BI) (a : A x) → Set ℓB}
--              (r : BI) (M : A r)
--              (N0 : (a0 : A bi0) → B bi0 a0)
--              (N1 : (a1 : A bi1) → B bi1 a1)
--              (NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)) →
--              BridgeP (λ x → (a : A x) → B x a) N0 N1
extentType :: TCM Type
extentType = do
  requireBridges "in extentType"
  t <- runNamesT [] $
       hPi' "lA" (el $ cl primLevel) (\ lA ->
       hPi' "lB" (el $ cl primLevel) $ \ lB ->
       hPi' "A" (primBridgeIntervalType --> (sort . tmSort <$> lA)) $ \ bA ->
       hPi' "B" (nPi' "x" primBridgeIntervalType $ \ x -> (el' lA (bA <@> x)) --> (sort . tmSort <$> lB) ) $ \bB ->
       nPi' "r" primBridgeIntervalType $ \ r ->
       -- below A r is an IApply elim instead of std argument, might come in handy?
       nPi' "M" (el' lA (bA <@@> (bA <@> cl primBIZero, bA <@> cl primBIOne, r) )) $ \bM ->
       nPi' "N0" (nPi' "a0" (el' lA (bA <@> cl primBIZero)) $ \a0 -> (el' lB (bB <@> cl primBIZero <@> a0))) $ \n0 ->
       nPi' "N1" (nPi' "a1" (el' lA (bA <@> cl primBIOne)) $ \a1 -> (el' lB (bB <@> cl primBIOne <@> a1))) $ \n1 ->
       nPi' "NN"
        (nPi' "a0" (el' lA (bA <@> cl primBIZero)) $ \a0 ->
         nPi' "a1" (el' lA (bA <@> cl primBIOne)) $ \a1 ->
         primBridgeIntervalType) $ \nn ->
       primBridgeIntervalType)
  return t
                                         
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
