{-# OPTIONS --cubical  -v tc.prim.hcomp.rec:25 #-} --  --guarded --bridges --no-fast-reduce

module All2 where

open import Cubical.Core.Everything
open import Cubical.Data.Bool


record myRec (A : Type) : Type where
  field
    smr : Bool → A
    lp : smr false ≡ smr false
open myRec public


-- module hcompRec (A : Type) (φ : I) (u : (i : I) → Partial φ (myRec A)) (u0 : myRec A) where

--   thephi = φ
--   here = hcomp {ℓ = _} {A = (myRec A)} {φ = φ} (λ i _ → u0) u0

--   hole : Bool
--   hole = {!!}

