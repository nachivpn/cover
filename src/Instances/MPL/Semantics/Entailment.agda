{-# OPTIONS --safe --without-K #-}

module Instances.MPL.Semantics.Entailment where

open import NonDistributiveAlgebras

open import Instances.MPL.System
import Instances.MPL.Semantics.Interpretation as Interpretation

-- Entailment in an algebraic model
_⨾_⊨ₐ_ : MPLAlgebra → Ctx → Form → Set₁
𝒫 ⨾ Γ ⊨ₐ a = ∀ V𝕡 → let open Interpretation 𝒫 V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment in all algebraic models
_⊨ₐ_ : Ctx → Form → Set₂
Γ ⊨ₐ a = ∀ 𝒫 → 𝒫 ⨾ Γ ⊨ₐ a
