{-# OPTIONS --safe --without-K #-}

module Instances.SL.Semantics.Entailment where

open import HeytingAlgebras

open import Instances.SL.System
import Instances.SL.Semantics.Interpretation as Interpretation

-- Entailment in a model
_⨾_⊨ₐ_ : SLAlgebra → Ctx → Form → Set₁
𝒜 ⨾ Γ ⊨ₐ a = ∀ V𝕡 → let open Interpretation 𝒜 V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment
_⊨ₐ_ : Ctx → Form → Set₂
Γ ⊨ₐ a = ∀ 𝒜 → 𝒜 ⨾ Γ ⊨ₐ a
