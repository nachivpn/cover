{-# OPTIONS --safe --without-K #-}

module NonDistributiveAlgebras where

open import Level using (0ℓ ; suc)
open import Relation.Binary.Lattice.Bundles renaming
  (BoundedMeetSemilattice to LBoundedMeetSemilattice
  ; BoundedLattice to LBoundedLattice)
open import Relation.Binary.Lattice.Structures
  using (IsBoundedLattice)
open import Relation.Binary.Definitions

open import Data.Product
  using (_,_ ; -,_ ; proj₁ ; proj₂)

private 1ℓ = suc 0ℓ

BoundedMeetSemilattice = LBoundedMeetSemilattice 1ℓ 0ℓ 0ℓ
module BoundedMeetSemilattice = LBoundedMeetSemilattice

BoundedLattice = LBoundedLattice 1ℓ 0ℓ 0ℓ
module BoundedLattice = LBoundedLattice

-- "Positive Logic" algebra
record PosLogAlgebra : Set₂ where

  field
    ℬ : BoundedMeetSemilattice

  open BoundedMeetSemilattice ℬ public

  field
    ⊥        : Carrier
    ⊥-least : ∀ {x} → ⊥ ≤ x

  field
    _∨_     : Carrier → Carrier → Carrier
    ∨-mon   : {x y x' y' : Carrier} → x ≤ x' → y ≤ y' → x ∨ y ≤ x' ∨ y'
    ∨-comm  : ∀ {x y} → x ∨ y ≤ y ∨ x
    ∨-wabsʳ : ∀ {x y} → x ∨ x ≤ x ∨ (x ∧ y)
    ∨-idemˡ : ∀ {x} → x ∨ x ≤ x

  ∨-wabsˡ : ∀ {x y} → (x ∨ (x ∧ y)) ≤ (x ∨ x)
  ∨-wabsˡ {x} {y} = ∨-mon refl (x∧y≤x x y)

  ∨-wabs : ∀ {x y} → (x ∨ (x ∧ y)) ≈ (x ∨ x)
  ∨-wabs {x} {y} = antisym ∨-wabsˡ ∨-wabsʳ

  ∨-wken₂ : ∀ {x y} → x ∨ x ≤ x ∨ y
  ∨-wken₂ {x} {y} = trans ∨-wabsʳ (∨-mon refl (x∧y≤y x y))

  ∨-wken₁ : ∀ {x y} → x ∨ x ≤ y ∨ x
  ∨-wken₁ = trans ∨-wken₂ ∨-comm

  ∨-least : ∀ x y z → x ≤ z → y ≤ z → (x ∨ y) ≤ z
  ∨-least _ _ _ p q = trans (∨-mon p q) ∨-idemˡ

  minimum : ∀ x → ⊥ ≤ x
  minimum _ = ⊥-least

-- "Lattice Logic" algebra
record LatLogAlgebra : Set₂ where

  field
    𝒫 : PosLogAlgebra

  open PosLogAlgebra 𝒫 public

  field
    ∨-idemʳ : ∀ {x} → x ≤ x ∨ x

  x≤x∨y : ∀ x y → x ≤ (x ∨ y)
  x≤x∨y x y = trans ∨-idemʳ ∨-wken₂

  y≤x∨y : ∀ x y → y ≤ (x ∨ y)
  y≤x∨y x y = trans ∨-idemʳ ∨-wken₁

  ℒ : BoundedLattice
  ℒ = record
    { Carrier = Carrier
    ; _≈_     = _≈_
    ; _≤_     = _≤_
    ; _∨_     = _∨_
    ; _∧_     = _∧_
    ; ⊤       = ⊤
    ; ⊥       = ⊥
    ; isBoundedLattice = record
      { isLattice = record
        { isPartialOrder = isPartialOrder
        ; supremum = λ x y → x≤x∨y x y , y≤x∨y x y , ∨-least x y
        ; infimum  = infimum
        }
      ; maximum   = maximum
      ; minimum   = minimum
      }
    }

module Properties where

  module _ (ℒ : BoundedLattice) where

    open BoundedLattice ℒ

    latLogAlgebra : LatLogAlgebra
    latLogAlgebra = record
      { 𝒫 = record
        { ℬ      = boundedMeetSemilattice
        ; ⊥       = ⊥
        ; ⊥-least = λ {x} → minimum x
        ; _∨_     = _∨_
        ; ∨-mon   = λ p q → ∨-least
            (trans p (x≤x∨y _ _))
            (trans q (y≤x∨y _ _))
        ; ∨-comm  = λ {x} {y} → ∨-least (y≤x∨y y x) (x≤x∨y y x)
        ; ∨-wabsʳ = λ {x} {y} → ∨-least (x≤x∨y x (x ∧ y)) (x≤x∨y x (x ∧ y))
        ; ∨-idemˡ = λ {x} → ∨-least refl refl
        }
      ; ∨-idemʳ = λ {x} → x≤x∨y x x
      }
