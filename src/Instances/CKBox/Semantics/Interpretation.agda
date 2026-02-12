{-# OPTIONS --safe #-}

open import HeytingAlgebras

open import Instances.CKBox.System
open import Data.Product using (_×_ ; _,_)

module Instances.CKBox.Semantics.Interpretation
  -- Model
  (𝒜 : CKBoxAlgebra)
  -- Valuation for atoms
  (V𝕡 : Atom → 𝒜 .CKBoxAlgebra.Carrier)  
  where

open CKBoxAlgebra 𝒜
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
