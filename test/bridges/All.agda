{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module All where

open import BridgePrims public
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat


module decomposeInterval (x y z : I) where
  
  toDec : I
  toDec = ~ x ∨ (y ∧ ~ z) ∨ i1


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
