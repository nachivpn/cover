{-# OPTIONS --safe #-}

open import Instances.IPL.System

open import Level using (0ℓ ; suc)
open import Relation.Binary.Lattice.Bundles renaming (HeytingAlgebra to LHeytingAlgebra)

module Instances.IPL.Semantics.Lib where

private 1ℓ = suc 0ℓ
HeytingAlgebra = LHeytingAlgebra 1ℓ 0ℓ 0ℓ
module HeytingAlgebra = LHeytingAlgebra

variable
  a b c d : Form
  i j : Atom
