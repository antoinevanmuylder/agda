{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module All where

open import BridgePrims public
open import Agda.Builtin.Bool


module decomposeInterval (x y z : I) where
  
  toDec : I
  toDec = ~ x ∨ (y ∧ ~ z) ∨ i1


  otherDec : I
  otherDec = toDec


module _ where

  bpartial1 : BPartial byes Bool
  bpartial1 = λ _ → true

  bpartial2 : BPartial byes Bool
  bpartial2 = λ _ → false

  
