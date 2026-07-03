{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.Calculus where

open import Instances.LatLog.System renaming
  ( Form to Ty
  ; ⊤ to 𝟙 ; ⊥ to 𝟘 ; _∧_ to _×_ ; _∨_ to _＋_
  ; hyp to var ; ⊤-I to unit ; ⊥-E to abort
  ; ∧-I to pair ; ∧-E1 to fst ; ∧-E2 to snd
  ; ∨-I1 to inl ; ∨-I2 to inr ; ∨-E to match) public

variable
  t t' t₁ t₂ u u' : Γ ⊢ a

Tm : Ctx → Ty → Set
Tm = _⊢_

pattern x₀   = var zero

open import Substitution Ty Tm var wkTm public

substTm : Sub Γ Δ → Tm Δ a → Tm Γ a
substTm s (var x)        = substVar s x
substTm s unit           = unit
substTm s (abort t)      = abort (substTm s t)
substTm s (pair t u)     = pair (substTm s t) (substTm s u)
substTm s (fst t)        = fst (substTm s t)
substTm s (snd t)        = snd (substTm s t)
substTm s (inl t)        = inl (substTm s t)
substTm s (inr t)        = inr (substTm s t)
substTm s (match t u u') = match (substTm s t) u u'
