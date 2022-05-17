{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module All where

open import BridgePrims public


module decomposeInterval (x y z : I) where
  
  toDec : I
  toDec = ~ x ∨ (y ∧ ~ z) ∨ i1
