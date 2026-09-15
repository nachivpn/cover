{-# OPTIONS --safe --without-K #-}

module Instances.CS4Box.Semantics.Entailment where

open import HeytingAlgebras

open import Instances.CS4Box.System
import Instances.CS4Box.Semantics.Interpretation as Interpretation

open import Data.Product using (_,_)

-- Entailment in a model
_⨾_⨾_⊨ₐ_ : CS4BoxAlgebra → Ctx → Ctx → Form → Set₁
𝒜 ⨾ Δ ⨾ Γ ⊨ₐ a = ∀ V𝕡 → let open Interpretation 𝒜 V𝕡 in ⟦ Δ , Γ ⟧c₂ ≤ ⟦ a ⟧

-- Entailment
_⨾_⊨ₐ_ : Ctx → Ctx → Form → Set₂
Δ ⨾ Γ ⊨ₐ a = ∀ 𝒜 → 𝒜 ⨾ Δ ⨾ Γ ⊨ₐ a
