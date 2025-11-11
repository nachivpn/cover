{-# OPTIONS --safe #-}

open import Instances.IPL.System
open import Instances.IPL.Semantics.Lib
import Instances.IPL.Semantics.Interpretation as Interpretation

module Instances.IPL.Semantics.Entailment
  where

-- Entailment in a model
_⨾_⊨_ : HeytingAlgebra → Ctx → Form → Set₁
ℋ ⨾ Γ ⊨ a = ∀ V𝕡 → let open Interpretation ℋ V𝕡 in ⟦ Γ ⟧c ≤ ⟦ a ⟧

-- Entailment
_⊨_ : Ctx → Form → Set₂
Γ ⊨ a = ∀ ℋ → ℋ ⨾ Γ ⊨ a
