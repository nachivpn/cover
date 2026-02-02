{-# OPTIONS --safe #-}

open import HeytingAlgebras

open import Instances.PLL.System
import Instances.PLL.Semantics.Interpretation as Interpretation

module Instances.PLL.Semantics.Entailment
  where

-- Entailment in a model
_⨾_⊨_ : PLLAlgebra → Ctx → Form → Set₁
𝒜 ⨾ Γ ⊨ a = ∀ V𝕡 → let open Interpretation 𝒜 V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment
_⊨_ : Ctx → Form → Set₂
Γ ⊨ a = ∀ 𝒜 → 𝒜 ⨾ Γ ⊨ a
