{-# OPTIONS --safe --without-K #-}

module Instances.CM.Semantics.Entailment where

open import HeytingAlgebras

open import Instances.CM.System
import Instances.CM.Semantics.Interpretation as Interpretation

-- Entailment in a model
_⨾_⊨ₐ_ : CMAlgebra → Ctx → Form → Set₁
𝒜 ⨾ Γ ⊨ₐ a = ∀ V𝕡 → let open Interpretation 𝒜 V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment
_⊨ₐ_ : Ctx → Form → Set₂
Γ ⊨ₐ a = ∀ 𝒜 → 𝒜 ⨾ Γ ⊨ₐ a
