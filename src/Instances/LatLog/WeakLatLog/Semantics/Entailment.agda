{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.WeakLatLog.Semantics.Entailment where

open import NonDistributiveAlgebras

open import Instances.LatLog.WeakLatLog.System
import Instances.LatLog.WeakLatLog.Semantics.Interpretation as Interpretation

-- Entailment in an algebraic model
_⨾_⊨ₐ_ : WeakLatLogAlgebra → Ctx → Form → Set₁
𝒜 ⨾ Γ ⊨ₐ a = ∀ V𝕡 → let open Interpretation 𝒜 V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment in all algebraic models
_⊨ₐ_ : Ctx → Form → Set₂
Γ ⊨ₐ a = ∀ 𝒜 → 𝒜 ⨾ Γ ⊨ₐ a
