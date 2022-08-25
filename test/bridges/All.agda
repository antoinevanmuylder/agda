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


