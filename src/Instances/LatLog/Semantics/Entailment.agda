{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.Semantics.Entailment where

open import NonDistributiveAlgebras

open import Instances.LatLog.System
import Instances.LatLog.Semantics.Interpretation as Interpretation

-- Entailment in an algebraic model
_⨾_⊨ₐ_ : BoundedLattice → Ctx → Form → Set₁
𝒫 ⨾ Γ ⊨ₐ a = ∀ V𝕡 → let open Interpretation 𝒫 V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment in all algebraic models
_⊨ₐ_ : Ctx → Form → Set₂
Γ ⊨ₐ a = ∀ 𝒫 → 𝒫 ⨾ Γ ⊨ₐ a
