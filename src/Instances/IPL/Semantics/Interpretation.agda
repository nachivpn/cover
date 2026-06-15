{-# OPTIONS --safe --without-K #-}

open import HeytingAlgebras

open import Instances.IPL.System

module Instances.IPL.Semantics.Interpretation
  -- Model
  (ℋ : HeytingAlgebra)
  -- Valuation for atoms
  (V𝕡 : Atom → ℋ .HeytingAlgebra.Carrier)  
  where

open HeytingAlgebra ℋ
  renaming ( Carrier to H
           ; ⊤ to ⊤'
           ; ⊥ to ⊥'
           ; _∧_ to _∧'_
           ; _∨_ to _∨'_
           ; _⇨_ to _⇒'_
           ) public

-- Interpretation of a formula
⟦_⟧ : Form → H
⟦ 𝕡 i ⟧   = V𝕡 i
⟦ ⊤ ⟧     = ⊤'
⟦ ⊥ ⟧     = ⊥'
⟦ a ⇒ b ⟧ = ⟦ a ⟧ ⇒' ⟦ b ⟧
⟦ a ∧ b ⟧ = ⟦ a ⟧ ∧' ⟦ b ⟧
⟦ a ∨ b ⟧ = ⟦ a ⟧ ∨' ⟦ b ⟧

-- Interpretation of a context
⟦_⟧c : Ctx → H
⟦ [] ⟧c     = ⊤'
⟦ Γ `, a ⟧c = ⟦ Γ ⟧c ∧' ⟦ a ⟧
