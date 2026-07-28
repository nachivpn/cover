{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.STPC.Conversion where

open import Init

open import Instances.LatLog.STPC.Calculus

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

  -- hoisting rules (permutation for certain introduction rules; rest are admissible)
  hoi-𝟘-＋1 : inl (abort t) ≈ abort {Γ} {a ＋ b} t
  hoi-𝟘-＋2 : inr (abort t) ≈ abort {Γ} {a ＋ b} t
  hoi-＋-＋1 : inl (match t t₁ t₂) ≈ match {Γ} {a} {b} {c ＋ d} t (inl t₁) (inl t₂)
  hoi-＋-＋2 : inr (match t t₁ t₂) ≈ match {Γ} {a} {b} {c ＋ d} t (inr t₁) (inr t₂)

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

open Conversion _≈_ ≈-is-equiv public

---------------------------------------
-- Substitution preserves conversion --
---------------------------------------

substVar-pres-≈ₛ : {s s' : Sub Δ Γ} (x : Var Γ a)
  → s ≈ₛ s' → substVar s x ≈ substVar s' x
substVar-pres-≈ₛ zero     (_ `, t≈t')
  = t≈t'
substVar-pres-≈ₛ (succ x) (s≈s' `, _)
  = substVar-pres-≈ₛ x s≈s'

substTm-pres-≈-left : {s s' : Sub Δ Γ} (t : Tm Γ a)
  → s ≈ₛ s' → substTm s t ≈ substTm s' t
substTm-pres-≈-left (var v)         s≈s'
  = substVar-pres-≈ₛ v s≈s'
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
  = ≈-trans (red-＋1 _ _ _) (≡-to-≈ (substTm-pres-∙ₛ ([] `, t) s u))
substTm-pres-≈-right s (red-＋2 t u u')
  = ≈-trans (red-＋2 _ _ _) (≡-to-≈ (substTm-pres-∙ₛ ([] `, t) s u'))
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
substTm-pres-≈-right s hoi-𝟘-＋1
  = hoi-𝟘-＋1
substTm-pres-≈-right s hoi-𝟘-＋2
  = hoi-𝟘-＋2
substTm-pres-≈-right s hoi-＋-＋1
  = hoi-＋-＋1
substTm-pres-≈-right s hoi-＋-＋2
  = hoi-＋-＋2
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
  → s ≈ₛ s' → t ≈ t' → substTm s t ≈ substTm s' t'
substTm-pres-≈ {s' = s'} {t} s≈s' t≈t'
  = ≈-trans (substTm-pres-≈-left t s≈s') (substTm-pres-≈-right s' t≈t')

------------------------------------
-- Admitted and derived equations --
------------------------------------

-- "strong eta for 𝟘"
eta-𝟘 : (t : [] `,  𝟘 ⊢ c) (s : Γ ⊢ 𝟘)
  → substTm ([] `, s) t ≈ abort s
eta-𝟘 (var v0)   s = exp-𝟘 (substTm ([] `, s) (var Var.zero))
eta-𝟘 unit       s = ≈-sym (exp-𝟙 (abort s))
eta-𝟘 (abort t)  s = ≈-trans (con-abort (eta-𝟘 t s)) per-𝟘-𝟘
eta-𝟘 (pair t u) s = ≈-sym (≈-trans (exp-× (abort _)) (con-pair
  (≈-trans per-𝟘-×1 (≈-sym (eta-𝟘 t s)))
  (≈-trans per-𝟘-×2 (≈-sym (eta-𝟘 u s)))))
eta-𝟘 (fst t)    s = ≈-trans (con-fst (eta-𝟘 t s)) per-𝟘-×1
eta-𝟘 (snd t)    s = ≈-trans (con-snd (eta-𝟘 t s)) per-𝟘-×2
eta-𝟘 (inl t)    s = ≈-trans (con-inl (eta-𝟘 t s)) hoi-𝟘-＋1
eta-𝟘 (inr t)    s = ≈-trans (con-inr (eta-𝟘 t s)) hoi-𝟘-＋2
eta-𝟘 (match t t₁ t₂) s = ≈-trans (con-match (eta-𝟘 t s) ≈-refl ≈-refl) per-𝟘-＋

-- "strong eta for ＋"
eta-＋ : (t : [] `, (a ＋ b) ⊢ c) (s : Γ ⊢ a ＋ b)
  → substTm ([] `, s) t ≈ match s (substTm ([] `, inl x₀) t) (substTm ([] `, inr x₀) t)
eta-＋ (var v0)   s = exp-＋ (substTm ([] `, s) (var Var.zero))
eta-＋ unit       s = ≈-sym (exp-𝟙 (match s _ _))
eta-＋ (abort t)  s = ≈-trans (con-abort (eta-＋ t s)) per-＋-𝟘
eta-＋ (pair t u) s = ≈-sym (≈-trans (exp-× (match s _ _)) (con-pair
  (≈-trans per-＋-×1 (≈-trans (con-match ≈-refl red-×1 red-×1) (≈-sym (eta-＋ t s))))
  (≈-trans per-＋-×2 (≈-trans (con-match ≈-refl red-×2 red-×2) (≈-sym (eta-＋ u s))))))
eta-＋ (fst t)    s = ≈-trans (con-fst (eta-＋ t s)) per-＋-×1
eta-＋ (snd t)    s = ≈-trans (con-snd (eta-＋ t s)) per-＋-×2
eta-＋ (inl t)    s = ≈-trans (con-inl (eta-＋ t s)) hoi-＋-＋1
eta-＋ (inr t)    s = ≈-trans (con-inr (eta-＋ t s)) hoi-＋-＋2
eta-＋ (match t u u') s = ≈-trans (con-match (eta-＋ t s) ≈-refl ≈-refl) per-＋-＋


