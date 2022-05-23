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


module _ (@tick x : BI) (smth : Bool) (@tick y : BI) where

  multi1 : BPartial (x =bi0 b∨ y =bi0 b∨ y =bi1) (atyp smth)


  
