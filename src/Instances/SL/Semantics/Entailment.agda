{-# OPTIONS --safe #-}

open import HeytingAlgebras

open import Instances.SL.System
import Instances.SL.Semantics.Interpretation as Interpretation

module Instances.SL.Semantics.Entailment
  where

-- Entailment in a model
_⨾_⊨_ : SLAlgebra → Ctx → Form → Set₁
𝒜 ⨾ Γ ⊨ a = ∀ V𝕡 → let open Interpretation 𝒜 V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment
_⊨_ : Ctx → Form → Set₂
Γ ⊨ a = ∀ 𝒜 → 𝒜 ⨾ Γ ⊨ a
