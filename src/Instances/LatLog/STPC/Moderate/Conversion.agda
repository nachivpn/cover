{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.STPC.Moderate.Conversion where

open import Init

open import Instances.LatLog.STPC.Calculus

open import Relation.Binary using (Setoid)

infix 10 _≈_

data _≈_ : Tm Γ a → Tm Γ a → Set where

  -- reduction rules
  red-×1 : fst (pair t u) ≈ t
  red-×2 : snd (pair t u) ≈ u
  red-＋1 : (t : Γ ⊢ a) (u : [] `, a ⊢ c) (u' : [] `, b ⊢ c) → match (inl t) u u' ≈ substTm ([] `, t) u
  red-＋2 : (t : Γ ⊢ b) (u : [] `, a ⊢ c) (u' : [] `, b ⊢ c) → match (inr t) u u' ≈ substTm ([] `, t) u'

  -- expansion rules
  exp-𝟙 : (t : Γ ⊢ 𝟙) → t ≈ unit
  exp-𝟘 : (t : Γ ⊢ 𝟘) → t ≈ abort t
  exp-× : (t : Γ ⊢ a × b) → t ≈ pair (fst t) (snd t)
  exp-＋ : (t : Γ ⊢ a ＋ b) → t ≈ match t (inl x₀) (inr x₀)

  -- permutation rules for match
  per-＋-𝟘  : abort (match t u u') ≈ match {c = c} t (abort u) (abort u')
  per-＋-×1 : fst (match t u u') ≈ match t (fst u) (fst u')
  per-＋-×2 : snd (match t u u') ≈ match t (snd u) (snd u')
  per-＋-＋  : match (match t t₁ t₂) u u' ≈ match t (match t₁ u u') (match t₂ u u')

  -- permutation rules for abort
  per-𝟘-𝟘  : abort (abort t) ≈ abort {a = a} t
  per-𝟘-×1 : fst {Γ} {a} {b} (abort t) ≈ abort {Γ} {a} t
  per-𝟘-×2 : snd {Γ} {a} {b} (abort t) ≈ abort {Γ} {b} t
  per-𝟘-＋  : match (abort t) u u' ≈ abort t

  -- congruence rules
  con-abort : t ≈ u → abort t ≈ abort {Γ} {a} u
  con-pair  : t ≈ t' → u ≈ u' → pair t u ≈ pair t' u'
  con-fst   : t ≈ u → fst t ≈ fst u
  con-snd   : t ≈ u → snd t ≈ snd u
  con-inl   : t ≈ u → inl t ≈ inl {Γ} {a} {b} u
  con-inr   : t ≈ u → inr t ≈ inr {Γ} {a} {b} u
  con-match : {s s' : Γ ⊢ a ＋ b} → s ≈ s' → t ≈ t' → u ≈ u' → match s t u ≈ match s' t' u'

  -- equivalence rules
  ≈-refl  : t ≈ t
  ≈-sym   : t ≈ u → u ≈ t
  ≈-trans : t ≈ u → u ≈ u' → t ≈ u'

≡-to-≈ : ∀ {t u : Tm Γ a} → t ≡ u → t ≈ u
≡-to-≈ ≡-refl = ≈-refl

≈-is-equiv : {Γ : Ctx} {a : Ty} → IsEquivalence (_≈_ {Γ} {a})
≈-is-equiv = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }

Tm-setoid : (Γ : Ctx) → (a : Ty) → Setoid _ _
Tm-setoid Γ a = record
  { Carrier       = Tm Γ a
  ; _≈_           = _≈_
  ; isEquivalence = ≈-is-equiv
  }
  
open Conversion _≈_ ≈-is-equiv public

------------------------------------
-- Weakening preserves conversion --
------------------------------------

wkTm-pres-≈ : (w : Γ ⊑ Γ') {t t' : Tm Γ a}
    → t ≈ t' → wkTm w t ≈ wkTm w t'
wkTm-pres-≈ w red-×1
  = red-×1
wkTm-pres-≈ w red-×2
  = red-×2
wkTm-pres-≈ w (red-＋1 t u u')
  = ≈-trans (red-＋1 (wkTm w t) u u') (≡-to-≈ (substTm-nat u ([] `, t) w))
wkTm-pres-≈ w (red-＋2 t u u')
  = ≈-trans (red-＋2 (wkTm w t) u u') (≡-to-≈ (substTm-nat u' ([] `, t) w))
wkTm-pres-≈ w (exp-𝟙 t)
  = exp-𝟙 (wkTm w t)
wkTm-pres-≈ w (exp-𝟘 t)
  = exp-𝟘 (wkTm w t)
wkTm-pres-≈ w (exp-× t)
  = exp-× (wkTm w t)
wkTm-pres-≈ w (exp-＋ t)
  = exp-＋ (wkTm w t)
wkTm-pres-≈ w per-＋-𝟘
  = per-＋-𝟘
wkTm-pres-≈ w per-＋-×1
  = per-＋-×1
wkTm-pres-≈ w per-＋-×2
  = per-＋-×2
wkTm-pres-≈ w per-＋-＋
  = per-＋-＋
wkTm-pres-≈ w per-𝟘-𝟘
  = per-𝟘-𝟘
wkTm-pres-≈ w per-𝟘-×1
  = per-𝟘-×1
wkTm-pres-≈ w per-𝟘-×2
  = per-𝟘-×2
wkTm-pres-≈ w per-𝟘-＋
  = per-𝟘-＋
wkTm-pres-≈ w (con-abort t≈t')
  = con-abort (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (con-pair t≈t' t≈t'')
  = con-pair (wkTm-pres-≈ w t≈t') (wkTm-pres-≈ w t≈t'')
wkTm-pres-≈ w (con-fst t≈t')
  = con-fst (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (con-snd t≈t')
  = con-snd (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (con-inl t≈t')
  = con-inl (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (con-inr t≈t')
  = con-inr (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (con-match t≈t' t≈t'' t≈t''')
  = con-match (wkTm-pres-≈ w t≈t') t≈t'' t≈t'''
wkTm-pres-≈ w ≈-refl = ≈-refl
wkTm-pres-≈ w (≈-sym t≈t')
  = ≈-sym (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (≈-trans t≈t' t≈t'')
  = ≈-trans (wkTm-pres-≈ w t≈t') (wkTm-pres-≈ w t≈t'')

---------------------------------------
-- Substitution preserves conversion --
---------------------------------------

substVar-pres-≈ˢ : {s s' : Sub Δ Γ} (x : Var Γ a)
  → s ≈ˢ s' → substVar s x ≈ substVar s' x
substVar-pres-≈ˢ zero     (_ `, t≈t')
  = t≈t'
substVar-pres-≈ˢ (succ x) (s≈s' `, _)
  = substVar-pres-≈ˢ x s≈s'

substTm-pres-≈-left : {s s' : Sub Δ Γ} (t : Tm Γ a)
  → s ≈ˢ s' → substTm s t ≈ substTm s' t
substTm-pres-≈-left (var v)         s≈s'
  = substVar-pres-≈ˢ v s≈s'
substTm-pres-≈-left unit            s≈s'
  = ≈-refl
substTm-pres-≈-left (fst t)         s≈s'
  = con-fst (substTm-pres-≈-left t s≈s')
substTm-pres-≈-left (snd t)         s≈s'
  = con-snd (substTm-pres-≈-left t s≈s')
substTm-pres-≈-left (pair t u)      s≈s'
  = con-pair (substTm-pres-≈-left t s≈s') (substTm-pres-≈-left u s≈s')
substTm-pres-≈-left (abort t)       s≈s'
  = con-abort (substTm-pres-≈-left t s≈s')
substTm-pres-≈-left (inl t)         s≈s'
  = con-inl (substTm-pres-≈-left t s≈s')
substTm-pres-≈-left (inr t)         s≈s'
  = con-inr (substTm-pres-≈-left t s≈s')
substTm-pres-≈-left (match t t₁ t₂) s≈s'
  = con-match (substTm-pres-≈-left t s≈s') ≈-refl ≈-refl
  
substTm-pres-≈-right : (s : Sub Γ Δ)
  → t ≈ u → substTm s t ≈  substTm s u
substTm-pres-≈-right s red-×1
  = red-×1
substTm-pres-≈-right s red-×2
  = red-×2
substTm-pres-≈-right s (red-＋1 t u u')
  = ≈-trans (red-＋1 _ _ _) (≡-to-≈ (substTm-pres-∙ˢ ([] `, t) s u))
substTm-pres-≈-right s (red-＋2 t u u')
  = ≈-trans (red-＋2 _ _ _) (≡-to-≈ (substTm-pres-∙ˢ ([] `, t) s u'))
substTm-pres-≈-right s (exp-𝟙 t)
  = exp-𝟙 (substTm s t)
substTm-pres-≈-right s (exp-𝟘 t)
  = exp-𝟘 (substTm s t)
substTm-pres-≈-right s (exp-× t)
  = exp-× (substTm s t)
substTm-pres-≈-right s (exp-＋ t)
  = exp-＋ (substTm s t)
substTm-pres-≈-right s per-＋-𝟘
  = per-＋-𝟘
substTm-pres-≈-right s per-＋-×1
  = per-＋-×1
substTm-pres-≈-right s per-＋-×2
  = per-＋-×2
substTm-pres-≈-right s per-＋-＋
  = per-＋-＋
substTm-pres-≈-right s per-𝟘-𝟘
  = per-𝟘-𝟘
substTm-pres-≈-right s per-𝟘-×1
  = per-𝟘-×1
substTm-pres-≈-right s per-𝟘-×2
  = per-𝟘-×2
substTm-pres-≈-right s per-𝟘-＋
  = per-𝟘-＋
substTm-pres-≈-right s (con-abort r)
  = con-abort (substTm-pres-≈-right s r)
substTm-pres-≈-right s (con-pair r r')
  = con-pair (substTm-pres-≈-right s r) (substTm-pres-≈-right s r')
substTm-pres-≈-right s (con-fst r)
  = con-fst (substTm-pres-≈-right s r)
substTm-pres-≈-right s (con-snd r)
  = con-snd (substTm-pres-≈-right s r)
substTm-pres-≈-right s (con-inl r)
  = con-inl (substTm-pres-≈-right s r)
substTm-pres-≈-right s (con-inr r)
  = con-inr (substTm-pres-≈-right s r)
substTm-pres-≈-right s (con-match r r₁ r₂)
  = con-match (substTm-pres-≈-right s r) r₁ r₂
substTm-pres-≈-right s ≈-refl
  = ≈-refl
substTm-pres-≈-right s (≈-sym r)
  = ≈-sym (substTm-pres-≈-right s r)
substTm-pres-≈-right s (≈-trans r r')
  = ≈-trans (substTm-pres-≈-right s r) (substTm-pres-≈-right s r')

substTm-pres-≈ : {s s' : Sub Δ Γ} {t t' : Tm Γ a}
  → s ≈ˢ s' → t ≈ t' → substTm s t ≈ substTm s' t'
substTm-pres-≈ {s' = s'} {t} s≈s' t≈t'
  = ≈-trans (substTm-pres-≈-left t s≈s') (substTm-pres-≈-right s' t≈t')



