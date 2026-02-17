{-# OPTIONS --safe #-}

open import HeytingAlgebras

open import Instances.CM.System
import Instances.CM.Semantics.Interpretation as Interpretation

module Instances.CM.Semantics.Entailment
  where

-- Entailment in a model
_⨾_⊨_ : CMAlgebra → Ctx → Form → Set₁
𝒜 ⨾ Γ ⊨ a = ∀ V𝕡 → let open Interpretation 𝒜 V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment
_⊨_ : Ctx → Form → Set₂
Γ ⊨ a = ∀ 𝒜 → 𝒜 ⨾ Γ ⊨ a
