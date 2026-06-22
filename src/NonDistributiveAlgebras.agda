{-# OPTIONS --safe --without-K #-}

module NonDistributiveAlgebras where

open import Level using (0ℓ ; suc)
open import Relation.Binary.Lattice.Bundles renaming
  (BoundedMeetSemilattice to LBoundedMeetSemilattice
  ; BoundedLattice to LBoundedLattice)
open import Relation.Binary.Definitions

private 1ℓ = suc 0ℓ

BoundedMeetSemilattice = LBoundedMeetSemilattice 1ℓ 0ℓ 0ℓ
module BoundedMeetSemilattice = LBoundedMeetSemilattice

BoundedLattice = LBoundedLattice 1ℓ 0ℓ 0ℓ
module BoundedLattice = LBoundedLattice

-- "Minimal Positive Logic" algebra
record MPLAlgebra : Set₂ where
  field
    ℬ : BoundedMeetSemilattice

  open BoundedMeetSemilattice ℬ public

  field
    ⊥       : Carrier
    _∨_     : Carrier → Carrier → Carrier
    minimum : Minimum _≤_ ⊥
    ∨-mon   : ∀ {x y x' y'} → x ≤ x' → y ≤ y' → (x ∨ y) ≤ (x' ∨ y')
    ∨-comm  : ∀ {x y} → x ∨ y ≤ y ∨ x
    ∨-idem  : ∀ {x} → x ∨ x ≤ x
    ∨-weak  : ∀ {x y} → x ∨ x ≤ x ∨ y

  ∨-least : ∀ {x y z} → x ≤ z → y ≤ z → (x ∨ y) ≤ z
  ∨-least p q = trans (∨-mon p q) ∨-idem
