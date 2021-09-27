{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce -v tc.reduce:31 #-}
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

-- INTRO
-- how to INTRO such a bridge? we somehow need a function p : (i:BI) → A i
-- such that p 0 = a0 and p 1 = a1 definitionally.
-- For paths, see checkPath defined in TypeChecking/Rules/Term.hs
-- It indeed checks the body p i of p in augmented context Gamma, i and ensures that endpoints are correct.



cst-t : BridgeP (λ i → Bool) true true
cst-t = λ i → true

cst-f : BridgeP (λ i → Bool) false false
cst-f = λ i → false

-- fail-cstbridge : BridgeP (λ i → Bool) true true
-- fail-cstbridge = λ i → false


-- ELIM
-- had to make BridgeP "non rigid" fwiw
-- had to add a BridgeP case when infering applications (similar to paths)
-- will it typecheck cartesian application? (non fresh subst)

applied-bridge : Bool
applied-bridge = cst-t bi0

-- | the type of 1 bridges with endpoints true true
bdg-t = BridgeP (λ i → Bool) true true

-- | the type of 2-bridges with endpoints cst-t ; cst-t
bdg-bdg-t = BridgeP (λ i → bdg-t) cst-t cst-t

cst-cst-t : bdg-bdg-t
cst-cst-t = λ i → cst-t


-- | should typecheck. but we don't have the border computation rule yet
disguised-id : bdg-bdg-t → bdg-bdg-t
disguised-id x = λ i → x i

-- should not typecheck? does not typecheck but for the wrong reason (missing border computation rule)
-- problem : bdg-bdg-t → bdg-t
-- problem = λ x → λ i → x i i


-- x ⊢ x   (BI weakening?)
-- x , i ⊢ x                                   constraints i ∉ x                OK
-- x : bdg-bdg-t, i : BI ⊢ x i : bdg-t         constraints i ∉ x i              hopefully affine constr gets gen
-- x : bdg-bdg-t, i : BI ⊢ (x i) i : bdg-t     constraints x i i[0/i] = true    need border rule!
-- x : bdg-bdg-t ⊢ λ i → x i i : bdg-t
-- ⊢ λ x i → x i i : bdg-bdg-t → bdg-t
