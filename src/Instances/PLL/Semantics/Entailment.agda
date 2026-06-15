{-# OPTIONS --safe --without-K #-}

module Instances.PLL.Semantics.Entailment where

open import HeytingAlgebras

open import Instances.PLL.System
import Instances.PLL.Semantics.Interpretation as Interpretation

-- Entailment in an algebraic model
_⨾_⊨_ : PLLAlgebra → Ctx → Form → Set₁
𝒜 ⨾ Γ ⊨ a = ∀ V𝕡 → let open Interpretation 𝒜 V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment in all algebraic models
_⊨_ : Ctx → Form → Set₂
Γ ⊨ a = ∀ 𝒜 → 𝒜 ⨾ Γ ⊨ a
