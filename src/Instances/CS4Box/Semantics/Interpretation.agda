{-# OPTIONS --safe --without-K #-}

open import HeytingAlgebras

open import Instances.CS4Box.System

module Instances.CS4Box.Semantics.Interpretation
  -- Model
  (𝒜 : CS4BoxAlgebra)
  -- Valuation for atoms
  (V𝕡 : Atom → 𝒜 .CS4BoxAlgebra.Carrier)  
  where

open import Data.Product using (_×_ ; _,_)

open CS4BoxAlgebra 𝒜
  using (_≤_)
  renaming ( Carrier to H
           ; ⊤ to ⊤'
           ; ⊥ to ⊥'
           ; _∧_ to _∧'_
           ; _∨_ to _∨'_
           ; _⇨_ to _⇒'_
           ; ◻_ to ◻'_
           ) public

-- Interpretation of a formula
⟦_⟧ : Form → H
⟦ 𝕡 i ⟧   = V𝕡 i
⟦ ⊤ ⟧     = ⊤'
⟦ ⊥ ⟧     = ⊥'
⟦ a ⇒ b ⟧ = ⟦ a ⟧ ⇒' ⟦ b ⟧
⟦ a ∧ b ⟧ = ⟦ a ⟧ ∧' ⟦ b ⟧
⟦ a ∨ b ⟧ = ⟦ a ⟧ ∨' ⟦ b ⟧
⟦ ◻ a   ⟧ = ◻' ⟦ a ⟧

-- Interpretation of a context
⟦_⟧c : Ctx → H
⟦ [] ⟧c     = ⊤'
⟦ Γ `, a ⟧c = ⟦ Γ ⟧c ∧' ⟦ a ⟧

-- Interpretation of a "dual" context
⟦_⟧c₂ : Ctx₂ → H
⟦ Δ , Γ ⟧c₂ = (◻' ⟦ Δ ⟧c) ∧' ⟦ Γ ⟧c

