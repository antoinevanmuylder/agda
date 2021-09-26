{-# OPTIONS --cubical --guarded --bridges -v tc.term:20 #-}
module BridgePrims where

-- this is a reproduction of test/Succeed/LaterPrims.agda and-or Agda.Primitive.Cubical
-- We add a few examples too.

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU)
open import Agda.Builtin.Bool

------------------------------------------------------------------------
-- Bridge interval BI and endpoints bi0 bi1
------------------------------------------------------------------------

{-# BUILTIN BRIDGEINTERVAL BI  #-}  -- BI : LockU

{-# BUILTIN BIZERO    bi0 #-}
{-# BUILTIN BIONE     bi1 #-}

-- I is treated as the type of booleans.
-- {-# COMPILE JS i0 = false #-}
-- {-# COMPILE JS i1 = true  #-}



------------------------------------------------------------------------
-- Type of heterogeneous bridges BridgeP betweend spec. endpoints
------------------------------------------------------------------------

postulate
  BridgeP : ∀ {ℓ} (A : BI → Set ℓ) → A bi0 → A bi1 → Set ℓ

{-# BUILTIN BRIDGEP        BridgeP     #-}

-- how to introduce such a bridge? we somehow need a function p : (i:BI) → A i
-- such that p 0 = a0 and p 1 = a1 definitionally.
-- For paths, see checkPath defined in TypeChecking/Rules/Term.hs
-- It indeed checks the body p i of p in augmented context Gamma, i and ensures that endpoints are correct.



cstbridge-true : BridgeP (λ i → Bool) true true
cstbridge-true = λ i → true

cstbridge-false : BridgeP (λ i → Bool) false false
cstbridge-false = λ i → false

-- fail-cstbridge : BridgeP (λ i → Bool) true true
-- fail-cstbridge = λ i → false


