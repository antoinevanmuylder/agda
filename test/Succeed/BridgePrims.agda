{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce -v tc.prim:30 #-}
module BridgePrims where

-- this is a reproduction of test/Succeed/LaterPrims.agda and-or Agda.Primitive.Cubical
-- We add a few examples too.

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU)
open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path



------------------------------------------------------------------------
-- Bridge interval BI and endpoints bi0 bi1
------------------------------------------------------------------------

{-# BUILTIN BRIDGEINTERVAL BI  #-}  -- BI : LockU

{-# BUILTIN BIZERO    bi0 #-}
{-# BUILTIN BIONE     bi1 #-}

-- I is treated as the type of booleans.
-- {-# COMPILE JS i0 = false #-}
-- {-# COMPILE JS i1 = true  #-}

-- note
-- weirdly enough (i:BI) → Bool has type Set

------------------------------------------------------------------------
-- Type of heterogeneous bridges BridgeP betweend spec. endpoints
------------------------------------------------------------------------

postulate
  BridgeP : ∀ {ℓ} (A : BI → Set ℓ) → A bi0 → A bi1 → Set ℓ

{-# BUILTIN BRIDGEP        BridgeP     #-}

-- INTRO RULE

-- how to INTRO such a bridge? we somehow need a function p : (i:BI) → A i
-- such that p 0 = a0 and p 1 = a1 definitionally.
-- For paths, see checkPath defined in TypeChecking/Rules/Term.hs
-- It indeed checks the body p i of p in augmented context Gamma, i and ensures that endpoints are correct.

-- intro rule says
-- a section of a bridgy line can be made into a bridge with expected endpoints
mk-bridge : ∀ {ℓ} (A : BI → Set ℓ) (f : (i : BI) → A i) → BridgeP A (f bi0) (f bi1)
mk-bridge = λ A f → (λ i → f i)


cst-t : BridgeP (λ i → Bool) true true
cst-t = λ i → true

cst-f : BridgeP (λ i → Bool) false false
cst-f = λ i → false

-- fail-cstbridge : BridgeP (λ i → Bool) true true
-- fail-cstbridge = λ i → false



-- ELIM RULE

-- had to make BridgeP "non rigid" fwiw
-- had to add a BridgeP case when infering applications (similar to paths)
-- will it typecheck cartesian application? (non fresh subst)

-- below P is a closed bridge so r does not appear in r I think
destr-bdg : ∀ {ℓ} {A : BI → Set ℓ} {a0 : A bi0} {a1 : A bi1}
            (r : BI) (P : BridgeP A a0 a1) → A r
destr-bdg r P = P r     

applied-bridge : Bool
applied-bridge = cst-t bi0

-- | the type of 1 bridges with endpoints true true
bdg-t = BridgeP (λ i → Bool) true true

-- | the type of 2-bridges with endpoints cst-t ; cst-t
bdg-bdg-t = BridgeP (λ i → bdg-t) cst-t cst-t

cst-cst-t : bdg-bdg-t
cst-cst-t = λ i → cst-t

-- the following should not typecheck. i not fresh for x i.
-- problem : bdg-bdg-t → bdg-t
-- problem = λ x i → x i i


-- x ⊢ x   (BI weakening?)
-- x , i ⊢ x                                   constraints i ∉ x                OK
-- x : bdg-bdg-t, i : BI ⊢ x i : bdg-t         constraints i ∉ x i              hopefully affine constr gets gen
-- x : bdg-bdg-t, i : BI ⊢ (x i) i : bdg-t     constraints x i i[0/i] = true    need border rule!
-- x : bdg-bdg-t ⊢ λ i → x i i : bdg-t
-- ⊢ λ x i → x i i : bdg-bdg-t → bdg-t


-- BORDER COMPUTATION RULE

-- Try C-c C-n this (normalize)
compute-border : bdg-bdg-t → bdg-t
compute-border x = x bi0

-- | This one should typecheck.
disguised-id : bdg-bdg-t → bdg-bdg-t
disguised-id = λ x i → x i

-- we try to state the border rule and prove it up to path equality
-- the proof should go by computation
-- attempt1 can not take paths over a bridgy line A : BI → Set ℓ
-- would be interesting to know if there are maps I -- BI in some models
-- border-rule : 
--   {ℓ : Level} {A : BI → Set ℓ} {a0 : A bi0} {a1 : A bi1}
--   (bdg : BridgeP A a0 a1) →
--   PathP A (bdg bi0) a0
-- border-rule = ?

-- attempt2 (constant bridgy line)
border-rule : 
  {ℓ : Level} {A : Set ℓ} {a0 a1 : A}
  (bdg : BridgeP (λ bi → A) a0 a1) →
  PathP (λ i → A) (bdg bi0) a0
border-rule = λ bdg i → bdg bi0



-- ETA COMPUTATION RULE

eta-rule : 
  {ℓ : Level} {A : Set ℓ} {a0 a1 : A}
  (bdg : BridgeP (λ bi → A) a0 a1) →
  PathP (λ i → BridgeP (λ bi → A) a0 a1) bdg (λ bi → bdg bi)
eta-rule = λ bdg i → bdg

eta-rule' : 
  {ℓ : Level} {A : BI → Set ℓ} {a0 : A bi0} {a1 : A bi1}
  (bdg : BridgeP (λ i → A i) a0 a1) →
  bdg ≡ λ i → bdg i
eta-rule' bdg = λ j → bdg


-- BETA COMPUTATION RULE

--  how can I check that BETA is valid??
-- beta-rule :
--   {ℓ : Level} {A : BI → Set ℓ}
--   (bi : BI) (M : BI → A i)

-- dummy-rel : BridgeP (λ bi → BI) bi0 bi1
-- dummy-rel = λ bi → bi
  

-- BRIDGES VS BRIDGES (relational extensionality for bridges)
-- the exchange rule should hold for bridge vars
module BridgeVBridge {ℓ} (BB : BI → BI → Set ℓ) (a : (i j : BI) → BB i j) where


  -- we compare the types of λ i j → a i j and λ j i → a i j and
  -- try to establish an equiuvalence between them

  -- i left to right. j bottom to top
  -- ----------
  -- |        |
  -- |        |
  -- |        |
  -- ----------


  -- λ i j → a i j is a bridge between the left side and the right side of the above square.
  laij : BridgeP
         (λ i →  BridgeP (λ j → BB i j) (a i bi0)  (a i bi1))
         (λ j → a bi0 j)
         (λ j → a bi1 j)
  laij = λ i j → a i j

  -- λ j i → a i j is a bridge between the bottom side and the top side of the above square.
  laji : BridgeP
         (λ j →  BridgeP (λ i → BB i j) (a bi0 j)  (a bi1 j))
         (λ i → a i bi0)
         (λ i → a i bi1)
  laji = λ j i → a i j

  -- this should work!
  exch-bdg :
   BridgeP (λ x →  BridgeP (λ y → BB x y) (a x bi0)  (a x bi1)) (λ y → a bi0 y) (λ y → a bi1 y) →
   BridgeP (λ y →  BridgeP (λ x → BB x y) (a bi0 y)  (a bi1 y)) (λ x → a x bi0) (λ x → a x bi1)
  exch-bdg p = λ y x → p x y

  exch-bdg' :
    BridgeP (λ y →  BridgeP (λ x → BB x y) (a bi0 y)  (a bi1 y)) (λ x → a x bi0) (λ x → a x bi1) → 
    BridgeP (λ x →  BridgeP (λ y → BB x y) (a x bi0)  (a x bi1)) (λ y → a bi0 y) (λ y → a bi1 y)
  exch-bdg' p = λ x y → p y x

  -- one inverse condition of the bdg versus bdg principle
  bdgVbdg : ∀ p →  p ≡ (exch-bdg' (exch-bdg p) )
  bdgVbdg p = λ i → p

  -- the other one:
  bdgVbdg' : ∀ p → p ≡ (exch-bdg (exch-bdg' p))
  bdgVbdg' p = λ i → p

-- the following should indeed raise I think
-- but not with an error 
-- " The following vars are not allowed in a later value applied to i : [j]
--   when checking that the expression bdg-bdg j i has type A j "
-- exchange-bdg : ∀ {ℓ} {A : BI → Set ℓ} {a0 : A bi0} {a1 : A bi1}
--                {bdg1 bdg2 : BridgeP A a0 a1}
--                (bdg-bdg : BridgeP (λ bi → BridgeP A a0 a1) bdg1 bdg2) →
--                BridgeP (λ bi → BridgeP A a0 a1) bdg1 bdg2
-- exchange-bdg = λ bdg-bdg → λ i j → bdg-bdg j i


-- BRIDGES vs PATHS
module BridgeVPath {ℓ} {A : BI → I → Set ℓ} {a : (r : BI) (i : I) → A r i} where
  
  -- λ r i → a r i is a bridge between paths
  lari : BridgeP
         (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1))
         (λ i → a bi0 i)
         (λ i → a bi1 i)
  lari = λ r i → a r i

  
  -- λ i r → a r i is a path between bridges
  lair : PathP
         (λ i →  BridgeP (λ r → A r i) (a bi0 i)  (a bi1 i))
         (λ r → a r i0)
         (λ r → a r i1)
  lair = λ i r → a r i

  bdgPath-to-pathBdg :
    BridgeP (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1)) (λ i → a bi0 i) (λ i → a bi1 i) →
    PathP (λ i →  BridgeP (λ r → A r i) (a bi0 i)  (a bi1 i)) (λ r → a r i0) (λ r → a r i1)
  bdgPath-to-pathBdg bp = λ i r → bp r i

  pathBdg-to-bdgPth :
    PathP (λ i →  BridgeP (λ r → A r i) (a bi0 i)  (a bi1 i)) (λ r → a r i0) (λ r → a r i1) →
    BridgeP (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1)) (λ i → a bi0 i) (λ i → a bi1 i)
  pathBdg-to-bdgPth = λ pb → λ r i → pb i r

  -- one inverse condition of bdg versus path principle
  bridgevPath : ∀ bp → PathP
                        (λ _ → BridgeP (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1)) (λ i → a bi0 i) (λ i → a bi1 i) )
                        bp (pathBdg-to-bdgPth (bdgPath-to-pathBdg bp))
  bridgevPath bp = λ x → bp

  -- the other one
  pathvBridge  : ∀ pb → pb ≡ bdgPath-to-pathBdg ( pathBdg-to-bdgPth pb )
  pathvBridge pb = λ i → pb



------------------------------------------------------------------------
-- extent primitive
------------------------------------------------------------------------

-- postulate
--   BridgeP : ∀ {ℓ} (A : BI → Set ℓ) → A bi0 → A bi1 → Set ℓ

--  primitive 
--  primComp : ∀ {ℓ} (A : (i : I) → Set (ℓ i)) {φ : I} (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1

primitive

  primExtent : ∀ {ℓA ℓB : Level} {A : (@tick x : BI) → Set ℓA} {B : (@tick x : BI) (a : A x) → Set ℓB} -- should spec. @tick here?
               (r : BI) (M : A r)
               (N0 : (a0 : A bi0) → B bi0 a0)
               (N1 : (a1 : A bi1) → B bi1 a1)
               (NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)) →
               B r M


module PlayExtent {ℓA ℓB : Level} {A : BI → Set ℓA} {B : (x : BI) (a : A x) → Set ℓB}
                  (N0 : (a0 : A bi0) → B bi0 a0) (N1 : (a1 : A bi1) → B bi1 a1) where
  
  -- we wish to show bridge-funext: an equivalence btw the two foll. types
  -- pointwise-related is a retract thanks to extent beta rule
  -- related-sections is a retract thanks to extent eta rule
  pointwise-related = (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)

  related-sections = BridgeP (λ x → (a : A x) → B x a) N0 N1

  -- bridge-funext, hard direction
  bf-hard : pointwise-related → related-sections
  bf-hard NN = λ r M → primExtent r M N0 N1 NN


  bf-easy : related-sections -> pointwise-related
  bf-easy p = λ a0 a1 aa x → p x (aa x)


  pointwise-related-retract : (H : pointwise-related) -> H ≡ bf-easy (bf-hard H)
  pointwise-related-retract H = λ i → H
  -- TODO: issue #2 on my fork: when computing under lambdas, types of vars are forgotten which messes up the fv analysis
  -- try C-u C-u C-C C-t the target type

  related-sections-retract : (q : related-sections) -> q ≡ bf-hard ( bf-easy q )
  related-sections-retract q = {!!}
    
------------------------------------------------------------------------
-- Gel Types
------------------------------------------------------------------------


primitive
  primGel : ∀ {ℓA ℓ} (r : BI) (A0 A1 : Set ℓA) (R : A0 → A1 → Set ℓ) → Set ℓ


-- primitive
--   primgel : ∀ {ℓA ℓ} {A0 A1 : Set ℓA} {R : A0 → A1 → Set ℓ}
--         (r : BI) (M0 : A0) (M1 : A1) (P : R M0 M1) →
--         Gel r A0 A1 R 



  

module PlayLater where

  -- open import LaterPrims Γ ⊢ M:A(r)    Γ\r, r:I ⊢ M:A(r)
  
  -- --there is no exchange rule for tick vars
  -- later-exch : ∀ {ℓ} {A : Set ℓ} →
  --              (  (@tick x : Tick) → (@tick y : Tick) → A ) →
  --              (  (@tick y : Tick) → (@tick x : Tick) → A )
  -- later-exch laxy = λ y x → laxy x y
  
