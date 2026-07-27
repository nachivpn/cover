{-# OPTIONS --safe --without-K #-}

open import NonDistributiveAlgebras

open import Instances.LatLog.WeakLatLog.System

module Instances.LatLog.WeakLatLog.Semantics.Interpretation
  -- Model
  (𝒜 : WeakLatLogAlgebra)
  -- Valuation for atoms
  (V𝕡 : Atom → 𝒜 .WeakLatLogAlgebra.Carrier)  
  where

open WeakLatLogAlgebra 𝒜
  renaming ( Carrier to H
           ; ⊤ to ⊤'
           ; ⊥ to ⊥'
           ; _∧_ to _∧'_
           ; _∨_ to _∨'_
           ) public

-- Interpretation of a formula
⟦_⟧ : Form → H
⟦ 𝕡 i ⟧   = V𝕡 i
⟦ ⊤ ⟧     = ⊤'
⟦ ⊥ ⟧     = ⊥'
⟦ a ∧ b ⟧ = ⟦ a ⟧ ∧' ⟦ b ⟧
⟦ a ∨ b ⟧ = ⟦ a ⟧ ∨' ⟦ b ⟧

-- Interpretation of a context
⟦_⟧c : Ctx → H
⟦ [] ⟧c     = ⊤'
⟦ Γ `, a ⟧c = ⟦ Γ ⟧c ∧' ⟦ a ⟧
