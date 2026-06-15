{-# OPTIONS --safe --without-K #-}

open import HeytingAlgebras

open import Instances.IPL.System
import Instances.IPL.Semantics.Interpretation as Interpretation

module Instances.IPL.Semantics.Entailment
  where

-- Entailment in an algebraic model
_⨾_⊨ₐ_ : HeytingAlgebra → Ctx → Form → Set₁
ℋ ⨾ Γ ⊨ₐ a = ∀ V𝕡 → let open Interpretation ℋ V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment in all algebraic models
_⊨ₐ_ : Ctx → Form → Set₂
Γ ⊨ₐ a = ∀ ℋ → ℋ ⨾ Γ ⊨ₐ a
