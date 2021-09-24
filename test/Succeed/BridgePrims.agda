{-# OPTIONS --cubical --guarded --bridges #-}
module BridgePrims where

-- this is a reproduction of test/Succeed/LaterPrims and-or Agda.Primitive.Cubical

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

{-# BUILTIN BRIDGEINTERVAL BI  #-}  -- BI : LockU

{-# BUILTIN BIZERO    bi0 #-}
{-# BUILTIN BIONE     bi1 #-}

-- I is treated as the type of booleans.
-- {-# COMPILE JS i0 = false #-}
-- {-# COMPILE JS i1 = true  #-}

postulate
  BridgeP : ∀ {ℓ} (A : BI → Set ℓ) → A bi0 → A bi1 → Set ℓ

-- {-# BUILTIN PATHP        PathP     #-}
