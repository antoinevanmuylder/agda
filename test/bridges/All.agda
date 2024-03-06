{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module All where

open import BridgePrims public
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat


module decomposeInterval (x y z : I) where

  toDec : I
  toDec = ~ x ∨ (y ∧ ~ z) ∨ i1

  toDec2 : I
  toDec2 = x ∧ (y ∨ z)


  otherDec : I
  otherDec = toDec


nnot : Bool → Bool
nnot false = true
nnot true = false

atyp : Bool → Type ℓ-zero
atyp false = Bool
atyp true = Nat

anelem : (x : Bool) → atyp x
anelem false = false
anelem true = zero

anelem' : (x : Bool) → atyp x
anelem' false = true
anelem' true = suc zero

module _ (smth : Bool) where


  bpartial1 : BPartial byes (atyp smth)
  bpartial1 = λ _ → anelem smth

  bpartial2 : BPartial byes (atyp smth)
  bpartial2 = λ _ → anelem' smth

  hey : BPartial byes Bool
  hey = λ _ → true

  hey2 : BPartial byes Bool
  hey2 = λ _ → nnot (nnot true)


module _ (q : BridgeP (λ _ → Bool) false true) (q' : BridgeP (λ _ → Bool) true false) (@tick x : BI) (smth : Bool) (@tick y : BI) where

  premulti1 : BPartial (x =bi0 b∨ y =bi0 b∨ y =bi1) Bool
  premulti1 (x = bi0) = q y
  premulti1 (y = bi0) = q x
  premulti1 (y = bi1) = true

  multi1 : BPartial (x =bi0 b∨ y =bi0 b∨ y =bi1) Bool
  multi1 = premulti1

  -- judgemental equality detects that on y=bi1 multi1 & multi2 differ.
  premulti2 : BPartial (x =bi0 b∨ y =bi0 b∨ y =bi1) Bool
  premulti2 (x = bi0) = q y
  premulti2 (y = bi0) = q x
  premulti2 (y = bi1) = q' x

  multi2 : BPartial (x =bi0 b∨ y =bi0 b∨ y =bi1) Bool
  multi2 = premulti2


module _ (x : I) (@tick y : BI) where

  amixcstr : MCstr
  amixcstr = ((x ∨ ~ x) ∧ i1) m∨ (y =bi0 b∨ bno)

  mixcstr2 : MCstr
  mixcstr2 = ((x ∨ ~ x) ∧ i0) m∨ (y =bi0 b∨ bno)

module _ where

  ampartial : MPartial ( i1 m∨ bno) Bool
  ampartial _ = false


module _ (i : I) (@tick r : BI) (j : I) (@tick s : BI) where

  mcstr1 : MCstr
  mcstr1 = i0 m∨ r =bi0

  mcstr2 : MCstr
  mcstr2 = i ∧ j m∨ bno

  notj : MCstr
  notj = ~ j m∨ bno

  yesi : MCstr
  yesi = i m∨ bno

  noti = ~ i m∨ bno
  yesr = i0 m∨ r =bi1

  notr = i0 m∨ r =bi0
  yess = i0 m∨ s =bi1

  toRed : I
  toRed = ~ i ∧ i

  complex : MCstr
  complex = i ∧ ~ j ∨ i0 m∨ s =bi0 b∨ s =bi1

-- dnfPhi  =  [(CSPLIT,[(1,False), (3,True)],[])]
-- dnfPsi  =  [(BSPLIT,[(0,False)],[]), (BSPLIT,[(0,True)],[])]
-- dnfZeta  =  [(CSPLIT,[(1,False), (3,True)],[]),
--              (BSPLIT,[(0,False)],[]), (BSPLIT,[(0,True)],[])]


module _ (smth : Bool) where


  mpartial1 : MPartial myes (atyp smth)
  mpartial1 = λ _ → anelem smth

  mpartial2 : MPartial myes (atyp smth)
  mpartial2 = λ _ → anelem' smth

  mhey : MPartial myes Bool
  mhey = λ _ → true

  mhey2 : MPartial myes Bool
  mhey2 = λ _ → nnot (nnot true)


module _ (q : BridgeP (λ _ → Bool) false true) (q' : BridgeP (λ _ → Bool) true false) (@tick x : BI) (smth : Bool) (@tick y : BI) where

  mpremulti1 : MPartial (i0 m∨ x =bi0 b∨ y =bi0 b∨ y =bi1) Bool
  mpremulti1 (x = bi0) = q y
  mpremulti1 (y = bi0) = q x
  mpremulti1 (y = bi1) = true

  mmulti1 : MPartial (i0 m∨ x =bi0 b∨ y =bi0 b∨ y =bi1) Bool
  mmulti1 = mpremulti1

  -- judgemental equality detects that on y=bi1 multi1 & multi2 differ.
  mpremulti2 : MPartial (i0 m∨ x =bi0 b∨ y =bi0 b∨ y =bi1) Bool
  mpremulti2 (x = bi0) = q y
  mpremulti2 (y = bi0) = q x
  mpremulti2 (y = bi1) = q' x

  mmulti2 : MPartial (i0 m∨ x =bi0 b∨ y =bi0 b∨ y =bi1) Bool
  mmulti2 = mpremulti2

module _  (i : I) (@tick r : BI) (p : false ≡ true) (j : I) where

  notp : true ≡ false
  notp = (λ i → p (~ i))



  am1pre : MPartial (i ∨ (~ i ∧ j) m∨ r =bi1) Bool
  am1pre (i = i1) = false
  am1pre (i = i0) (j = i1) = true
  am1pre (r = bi1) = p  (~ i)

  am1 = am1pre

  am2pre : MPartial (i ∨ (~ i ∧ j) m∨ r =bi1) Bool
  am2pre (i = i1) = notp i
  am2pre (i = i0) (j = i1) = notp i
  am2pre (r = bi1) = notp i

  am2 = am2pre



-- module _ (ℓ : Level) (A : Type ℓ) (φ : I) (u : ∀ i → Partial φ A) (u0 : A) (b : Bool)  where

  -- toreduce : A
  -- toreduce = hcomp u u0


module _ {ℓA ℓB} (φ ψ : I) (A : Type ℓA) (T : Partial φ (Type ℓB)) (e : PartialP φ (λ o → T o ≃ A))  (u : ∀ (i : I) → Partial ψ (primGlue A T e)) (u0 : primGlue A T e) where

  anchor : Bool
  anchor = true

primitive
  primRefoldMhocom : ∀ {ℓ} {T : Type ℓ} → T → T
module _ {ℓ : Level} {T : Type ℓ} {φ : I} (u : (i : I) → MPartial (φ m∨ bno) T) (u0 : T) where

  postulate
    thing : MHolds (embdI φ)
  -- thing = {!!}

  hole : T
  hole = primRefoldMhocom (mhocom {ℓ = ℓ} {A = T} {ζ = φ m∨ bno} u (u i0 thing) )

module _ {ℓ : Level} {T : Type ℓ} {φ : I} (@tick x : BI) (u : (i : I) → MPartial (φ m∨ (x =bi1)) T) (u0 : T) where

  postulate
    thing2 : MHolds (φ m∨ (x =bi1))
  -- thing = {!!}

  hole2 : T
  hole2 = primRefoldMhocom (mhocom {ℓ = ℓ} {A = T} {ζ = φ m∨ (x =bi1)} u (u i0 thing2) )

