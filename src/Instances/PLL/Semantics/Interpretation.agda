{-# OPTIONS --safe --without-K #-}

open import HeytingAlgebras

open import Instances.PLL.System

module Instances.PLL.Semantics.Interpretation
  -- Model
  (𝒜 : PLLAlgebra)
  -- Valuation for atoms
  (V𝕡 : Atom → 𝒜 .PLLAlgebra.Carrier)  
  where

open PLLAlgebra 𝒜
  renaming ( Carrier to H
           ; ⊤ to ⊤'
           ; ⊥ to ⊥'
           ; _∧_ to _∧'_
           ; _∨_ to _∨'_
           ; _⇨_ to _⇒'_
           ; ◇_ to ◇'_
           ) public

-- Interpretation of a formula
⟦_⟧ : Form → H
⟦ 𝕡 i ⟧   = V𝕡 i
⟦ ⊤ ⟧     = ⊤'
⟦ ⊥ ⟧     = ⊥'
⟦ a ⇒ b ⟧ = ⟦ a ⟧ ⇒' ⟦ b ⟧
⟦ a ∧ b ⟧ = ⟦ a ⟧ ∧' ⟦ b ⟧
⟦ a ∨ b ⟧ = ⟦ a ⟧ ∨' ⟦ b ⟧
⟦ ◇ a   ⟧ = ◇' ⟦ a ⟧

-- Interpretation of a context
⟦_⟧c : Ctx → H
⟦ [] ⟧c     = ⊤'
⟦ Γ `, a ⟧c = ⟦ Γ ⟧c ∧' ⟦ a ⟧
