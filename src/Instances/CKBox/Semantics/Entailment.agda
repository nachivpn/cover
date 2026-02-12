{-# OPTIONS --safe #-}

open import HeytingAlgebras

open import Instances.CKBox.System
import Instances.CKBox.Semantics.Interpretation as Interpretation

open import Data.Product using (_,_)

module Instances.CKBox.Semantics.Entailment
  where

-- Entailment in a model
_⨾_⨾_⊨_ : CKBoxAlgebra → Ctx → Ctx → Form → Set₁
𝒜 ⨾ Δ ⨾ Γ ⊨ a = ∀ V𝕡 → let open Interpretation 𝒜 V𝕡 in ⟦ Δ , Γ ⟧c₂ ≤ ⟦ a ⟧

-- Entailment
_⨾_⊨_ : Ctx → Ctx → Form → Set₂
Δ ⨾ Γ ⊨ a = ∀ 𝒜 → 𝒜 ⨾ Δ ⨾ Γ ⊨ a
