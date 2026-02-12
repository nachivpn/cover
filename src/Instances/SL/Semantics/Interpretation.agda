{-# OPTIONS --safe #-}

open import HeytingAlgebras

open import Instances.SL.System

module Instances.SL.Semantics.Interpretation
  -- Model
  (𝒜 : SLAlgebra)
  -- Valuation for atoms
  (V𝕡 : Atom → 𝒜 .SLAlgebra.Carrier)  
  where

open SLAlgebra 𝒜
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
