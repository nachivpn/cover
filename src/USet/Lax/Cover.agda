{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.NFrame as NF
import USet.Localized as USetLoc

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

module USet.Lax.Cover
  {W     : Set}
  {_⊆_   : (w w' : W) → Set}
  (𝕎i   : Preorder W _⊆_)
  -- For the lax modality
  (N◇    : W → Set)
  (_∈◇_  : (v : W) {w : W} → N◇ w → Set)
  (Nuc◇  : NF.Nuclear 𝕎i N◇ _∈◇_)
  where

open import USet.Base 𝕎i

MNF◇ = Nuc◇ .NF.Nuclear.refinement

open import USet.Cover 𝕎i N◇ _∈◇_ MNF◇
  renaming
    (𝒞' to ◇'
    ; map𝒞' to ◇'-map
    ) public

module LocalizedCover
  (N₊   : W → Set)
  (_∈₊_ : (v : W) {w : W} → N₊ w → Set)
  (Nuc₊ : NF.Nuclear 𝕎i N₊ _∈₊_)
  (let open USetLoc 𝕎i N₊ _∈₊_ Nuc₊)
  (◇'-localize : {A : USet} → 𝒥' (◇' A) →̇ ◇' (𝒥' A))
  where

  open LUSet

  ◇₊_ : LUSet → LUSet
  ◇₊ (luset A lA) = luset (◇' A) (◇'-map lA ∘' ◇'-localize {A})

  ◇₊-map : {X Y : LUSet} → X →̇₊ Y → (◇₊ X) →̇₊ (◇₊ Y)
  ◇₊-map = ◇'-map
