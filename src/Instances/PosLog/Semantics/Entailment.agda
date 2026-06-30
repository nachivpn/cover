{-# OPTIONS --safe --without-K #-}

module Instances.PosLog.Semantics.Entailment where

open import NonDistributiveAlgebras

open import Instances.PosLog.System
import Instances.PosLog.Semantics.Interpretation as Interpretation

-- Entailment in an algebraic model
_⨾_⊨ₐ_ : PosLogAlgebra → Ctx → Form → Set₁
𝒜 ⨾ Γ ⊨ₐ a = ∀ V𝕡 → let open Interpretation 𝒜 V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment in all algebraic models
_⊨ₐ_ : Ctx → Form → Set₂
Γ ⊨ₐ a = ∀ 𝒜 → 𝒜 ⨾ Γ ⊨ₐ a
