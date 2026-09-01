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

open Composition substTm public -- exports _∙ˢ_

substVar-pres-idˢ : (x : Var Γ a) → substVar idˢ x ≡ var x
substVar-pres-idˢ zero     = ≡-refl
substVar-pres-idˢ (succ x) = ≡-trans (substVar-nat x idˢ freshWk) (≡-trans
  (≡-cong (wkTm freshWk) (substVar-pres-idˢ x))
  (≡-cong var (wkIncr x)))

substTm-pres-idˢ : (t : Tm Γ a) → substTm idˢ t ≡ t
substTm-pres-idˢ (var x)         = substVar-pres-idˢ x
substTm-pres-idˢ unit            = ≡-refl
substTm-pres-idˢ (fst t)         = ≡-cong fst (substTm-pres-idˢ t)
substTm-pres-idˢ (snd t)         = ≡-cong snd (substTm-pres-idˢ t)
substTm-pres-idˢ (pair t u)      = ≡-cong₂ pair (substTm-pres-idˢ t) (substTm-pres-idˢ u)
substTm-pres-idˢ (abort t)       = ≡-cong abort (substTm-pres-idˢ t)
substTm-pres-idˢ (inl t)         = ≡-cong inl (substTm-pres-idˢ t)
substTm-pres-idˢ (inr t)         = ≡-cong inr (substTm-pres-idˢ t)
substTm-pres-idˢ (match t t₁ t₂) = ≡-cong (λ s → match s t₁ t₂) (substTm-pres-idˢ t)

substVarPres∙ˢ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (x : Var Γ a)
  → substVar (s ∙ˢ s') x ≡ substTm s' (substVar s x)
substVarPres∙ˢ (s `, x) s' zero      = ≡-refl
substVarPres∙ˢ (s `, x) s' (succ x₁) = substVarPres∙ˢ s s' x₁

substTm-pres-∙ˢ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (t : Tm Γ a)
  → substTm (s ∙ˢ s') t ≡ substTm s' (substTm s t)
substTm-pres-∙ˢ s s' (var x)
  = substVarPres∙ˢ s s' x
substTm-pres-∙ˢ s s' unit
  = ≡-refl
substTm-pres-∙ˢ s s' (fst t)
  = ≡-cong fst (substTm-pres-∙ˢ s s' t)
substTm-pres-∙ˢ s s' (snd t)
  = ≡-cong snd (substTm-pres-∙ˢ s s' t)
substTm-pres-∙ˢ s s' (pair t u)
  = ≡-cong₂ pair (substTm-pres-∙ˢ s s' t) (substTm-pres-∙ˢ s s' u)
substTm-pres-∙ˢ s s' (abort t)
  = ≡-cong abort (substTm-pres-∙ˢ s s' t)
substTm-pres-∙ˢ s s' (inl t)
  = ≡-cong inl (substTm-pres-∙ˢ s s' t)
substTm-pres-∙ˢ s s' (inr t)
  = ≡-cong inr (substTm-pres-∙ˢ s s' t)
substTm-pres-∙ˢ s s' (match t t₁ t₂)
  = ≡-cong (λ s → match s t₁ t₂) (substTm-pres-∙ˢ s s' t)


substTm-nat : (t : Tm Γ a) (s : Sub Δ Γ) (w : Δ ⊑ Δ')
  → substTm (wkSub w s) t ≡ wkTm w (substTm s t)
substTm-nat (var x)     s w
  = substVar-nat x s w
substTm-nat unit        s w
  = ≡-refl
substTm-nat (abort t)   s w
  = ≡-cong abort (substTm-nat t s w)
substTm-nat (pair t t') s w
  = ≡-cong₂ pair (substTm-nat t s w) (substTm-nat t' s w)
substTm-nat (fst t)     s w
  = ≡-cong fst (substTm-nat t s w)
substTm-nat (snd t)     s w
  = ≡-cong snd (substTm-nat t s w)
substTm-nat (inl t)     s w
  = ≡-cong inl (substTm-nat t s w)
substTm-nat (inr t)     s w
  = ≡-cong inr (substTm-nat t s w)
substTm-nat (match u t₁ t₂) s w
  = ≡-cong (λ z → match z t₁ t₂) (substTm-nat u s w)
