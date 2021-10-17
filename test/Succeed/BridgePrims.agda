{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce -v tc.conv.term:60 #-}
module BridgePrims where

-- this is a reproduction of test/Succeed/LaterPrims.agda and-or Agda.Primitive.Cubical
-- We add a few examples too.

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU)
open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Primitive.Cubical using (PathP)



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


-- BORDER computation rule. Try C-c C-n this (normalize)
compute-border : bdg-bdg-t → bdg-t
compute-border x = x bi0

-- | This one should typecheck.
disguised-id : bdg-bdg-t → bdg-bdg-t
disguised-id = λ x i → x i

-- we try to state the rule and prove it up to path equality
-- the proof should go by computation
-- ATTEMPT1 can not take paths over a bridgy line A : BI → Set ℓ
-- would be interesting to know if there are maps I -- BI in some models
-- border-rule : 
--   {ℓ : Level} {A : BI → Set ℓ} {a0 : A bi0} {a1 : A bi1}
--   (bdg : BridgeP A a0 a1) →
--   PathP A (bdg bi0) a0
-- border-rule = ?

-- ATTEMPT2 (constant bridgy line)
border-rule : 
  {ℓ : Level} {A : Set ℓ} {a0 a1 : A}
  (bdg : BridgeP (λ bi → A) a0 a1) →
  PathP (λ i → A) (bdg bi0) a0
border-rule = λ bdg i → bdg bi0



-- ETA computation rule.
eta-rule : 
  {ℓ : Level} {A : Set ℓ} {a0 a1 : A}
  (bdg : BridgeP (λ bi → A) a0 a1) →
  PathP (λ i → BridgeP (λ bi → A) a0 a1) bdg (λ bi → bdg bi)
eta-rule = λ bdg i → bdg

-- BETA computation rule. how can I check that BETA is valid??
-- beta-rule :
--   {ℓ : Level} {A : BI → Set ℓ}
--   (bi : BI) (M : BI → A i)

-- dummy-rel : BridgeP (λ bi → BI) bi0 bi1
-- dummy-rel = λ bi → bi
  


-- should not typecheck. i not fresh for x i.
-- problem : bdg-bdg-t → bdg-t
-- problem = λ x i → x i i


-- x ⊢ x   (BI weakening?)
-- x , i ⊢ x                                   constraints i ∉ x                OK
-- x : bdg-bdg-t, i : BI ⊢ x i : bdg-t         constraints i ∉ x i              hopefully affine constr gets gen
-- x : bdg-bdg-t, i : BI ⊢ (x i) i : bdg-t     constraints x i i[0/i] = true    need border rule!
-- x : bdg-bdg-t ⊢ λ i → x i i : bdg-t
-- ⊢ λ x i → x i i : bdg-bdg-t → bdg-t
