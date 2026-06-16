{-# OPTIONS --safe --without-K #-}

open import NonDistributiveAlgebras

open import Instances.LatLog.System

module Instances.LatLog.Semantics.Interpretation
  -- Model
  (ℒ : BoundedLattice)
  -- Valuation for atoms
  (V𝕡 : Atom → ℒ .BoundedLattice.Carrier)  
  where

open BoundedLattice ℒ
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
