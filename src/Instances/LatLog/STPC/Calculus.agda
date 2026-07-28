{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.STPC.Calculus where

open import Init
    
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

open Composition substTm public -- exports _∙ₛ_

substVar-pres-idₛ : (x : Var Γ a) → substVar idₛ x ≡ var x
substVar-pres-idₛ zero     = ≡-refl
substVar-pres-idₛ (succ x) = ≡-trans (substVar-nat x idₛ freshWk) (≡-trans
  (≡-cong (wkTm freshWk) (substVar-pres-idₛ x))
  (≡-cong var (wkIncr x)))

substTm-pres-idₛ : (t : Tm Γ a) → substTm idₛ t ≡ t
substTm-pres-idₛ (var x)         = substVar-pres-idₛ x
substTm-pres-idₛ unit            = ≡-refl
substTm-pres-idₛ (fst t)         = ≡-cong fst (substTm-pres-idₛ t)
substTm-pres-idₛ (snd t)         = ≡-cong snd (substTm-pres-idₛ t)
substTm-pres-idₛ (pair t u)      = ≡-cong₂ pair (substTm-pres-idₛ t) (substTm-pres-idₛ u)
substTm-pres-idₛ (abort t)       = ≡-cong abort (substTm-pres-idₛ t)
substTm-pres-idₛ (inl t)         = ≡-cong inl (substTm-pres-idₛ t)
substTm-pres-idₛ (inr t)         = ≡-cong inr (substTm-pres-idₛ t)
substTm-pres-idₛ (match t t₁ t₂) = ≡-cong (λ s → match s t₁ t₂) (substTm-pres-idₛ t)

substVarPres∙ₛ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (x : Var Γ a)
  → substVar (s ∙ₛ s') x ≡ substTm s' (substVar s x)
substVarPres∙ₛ (s `, x) s' zero      = ≡-refl
substVarPres∙ₛ (s `, x) s' (succ x₁) = substVarPres∙ₛ s s' x₁

substTm-pres-∙ₛ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (t : Tm Γ a)
  → substTm (s ∙ₛ s') t ≡ substTm s' (substTm s t)
substTm-pres-∙ₛ s s' (var x)
  = substVarPres∙ₛ s s' x
substTm-pres-∙ₛ s s' unit
  = ≡-refl
substTm-pres-∙ₛ s s' (fst t)
  = ≡-cong fst (substTm-pres-∙ₛ s s' t)
substTm-pres-∙ₛ s s' (snd t)
  = ≡-cong snd (substTm-pres-∙ₛ s s' t)
substTm-pres-∙ₛ s s' (pair t u)
  = ≡-cong₂ pair (substTm-pres-∙ₛ s s' t) (substTm-pres-∙ₛ s s' u)
substTm-pres-∙ₛ s s' (abort t)
  = ≡-cong abort (substTm-pres-∙ₛ s s' t)
substTm-pres-∙ₛ s s' (inl t)
  = ≡-cong inl (substTm-pres-∙ₛ s s' t)
substTm-pres-∙ₛ s s' (inr t)
  = ≡-cong inr (substTm-pres-∙ₛ s s' t)
substTm-pres-∙ₛ s s' (match t t₁ t₂)
  = ≡-cong (λ s → match s t₁ t₂) (substTm-pres-∙ₛ s s' t)
