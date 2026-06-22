{-# OPTIONS --safe --without-K #-}

open import NonDistributiveAlgebras

open import Instances.MPL.System

module Instances.MPL.Semantics.Interpretation
  -- Model
  (𝒫 : MPLAlgebra)
  -- Valuation for atoms
  (V𝕡 : Atom → 𝒫 .MPLAlgebra.Carrier)  
  where

open MPLAlgebra 𝒫
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
