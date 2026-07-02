{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.Conversion where

open import Relation.Binary.PropositionalEquality
  using    (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong)

open import Instances.LatLog.System renaming
  ( ⊤ to 𝟙 ; ⊥ to 𝟘 ; _∧_ to _×_ ; _∨_ to _+_
  ; hyp to var ; ⊤-I to unit ; ⊥-E to abort
  ; ∧-I to pair ; ∧-E1 to fst ; ∧-E2 to snd
  ; ∨-I1 to inl ; ∨-I2 to inr ; ∨-E to match)

variable
  t t' t₁ t₂ u u' : Γ ⊢ a

Tm : Ctx → Form → Set
Tm = _⊢_

pattern x₀   = var zero

open import Substitution Form Tm var wkTm

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

data _≈_ : Tm Γ a → Tm Γ a → Set where

  -- reduction rules
  red-×1 : fst (pair t u) ≈ t
  red-×2 : snd (pair t u) ≈ u
  red-+1 : (t : Γ ⊢ a) (u : [] `, a ⊢ c) (u' : [] `, b ⊢ c) → match (inl t) u u' ≈ substTm ([] `, t) u
  red-+2 : (t : Γ ⊢ b) (u : [] `, a ⊢ c) (u' : [] `, b ⊢ c) → match (inr t) u u' ≈ substTm ([] `, t) u'

  -- expansion rules
  exp-𝟙 : (t : Γ ⊢ 𝟙) → t ≈ unit
  exp-𝟘 : (t : Γ ⊢ 𝟘) → t ≈ abort t
  exp-× : (t : Γ ⊢ a × b) → t ≈ pair (fst t) (snd t)
  exp-+ : (t : Γ ⊢ a + b) → t ≈ match t (inl x₀) (inr x₀)

  -- permutation rules for match
  per-+-𝟘  : abort (match t u u') ≈ match {c = c} t (abort u) (abort u')
  per-+-×1 : fst (match t u u') ≈ match t (fst u) (fst u')
  per-+-×2 : snd (match t u u') ≈ match t (snd u) (snd u')
  per-+-+  : match (match t t₁ t₂) u u' ≈ match t (match t₁ u u') (match t₂ u u')

  -- permutation rules for abort
  per-𝟘-𝟘  : abort (abort t) ≈ abort {a = a} t
  per-𝟘-×1 : fst {Γ} {a} {b} (abort t) ≈ abort {Γ} {a} t
  per-𝟘-×2 : snd {Γ} {a} {b} (abort t) ≈ abort {Γ} {b} t
  per-𝟘-+  : match (abort t) u u' ≈ abort t

  -- hoisting rules (permutation for certain introduction rules; rest are admissible)
  hoi-𝟘-+1 : inl (abort t) ≈ abort {Γ} {a + b} t
  hoi-𝟘-+2 : inr (abort t) ≈ abort {Γ} {a + b} t
  hoi-+-+1 : inl (match t t₁ t₂) ≈ match {Γ} {a} {b} {c + d} t (inl t₁) (inl t₂)
  hoi-+-+2 : inr (match t t₁ t₂) ≈ match {Γ} {a} {b} {c + d} t (inr t₁) (inr t₂)

  -- congruence rules
  con-abort : t ≈ u → abort t ≈ abort {Γ} {a} u
  con-pair  : t ≈ t' → u ≈ u' → pair t u ≈ pair t' u'
  con-fst   : t ≈ u → fst t ≈ fst u
  con-snd   : t ≈ u → snd t ≈ snd u
  con-inl   : t ≈ u → inl t ≈ inl {Γ} {a} {b} u
  con-inr   : t ≈ u → inr t ≈ inr {Γ} {a} {b} u
  con-match : {s s' : Γ ⊢ a + b} → s ≈ s' → t ≈ t' → u ≈ u' → match s t u ≈ match s' t' u'

  -- equivalence rules
  ≈-refl  : t ≈ t
  ≈-sym   : t ≈ u → u ≈ t
  ≈-trans : t ≈ u → u ≈ u' → t ≈ u'

≡-to-≈ : ∀ {t u : Tm Γ a} → t ≡ u → t ≈ u
≡-to-≈ ≡-refl = ≈-refl

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
eta-𝟘 (inl t)    s = ≈-trans (con-inl (eta-𝟘 t s)) hoi-𝟘-+1
eta-𝟘 (inr t)    s = ≈-trans (con-inr (eta-𝟘 t s)) hoi-𝟘-+2
eta-𝟘 (match t t₁ t₂) s = ≈-trans (con-match (eta-𝟘 t s) ≈-refl ≈-refl) per-𝟘-+

-- "strong eta for +"
eta-+ : (t : [] `, (a + b) ⊢ c) (s : Γ ⊢ a + b)
  → substTm ([] `, s) t ≈ match s (substTm ([] `, inl x₀) t) (substTm ([] `, inr x₀) t)
eta-+ (var v0)   s = exp-+ (substTm ([] `, s) (var Var.zero))
eta-+ unit       s = ≈-sym (exp-𝟙 (match s _ _))
eta-+ (abort t)  s = ≈-trans (con-abort (eta-+ t s)) per-+-𝟘
eta-+ (pair t u) s = ≈-sym (≈-trans (exp-× (match s _ _)) (con-pair
  (≈-trans per-+-×1 (≈-trans (con-match ≈-refl red-×1 red-×1) (≈-sym (eta-+ t s))))
  (≈-trans per-+-×2 (≈-trans (con-match ≈-refl red-×2 red-×2) (≈-sym (eta-+ u s))))))
eta-+ (fst t)    s = ≈-trans (con-fst (eta-+ t s)) per-+-×1
eta-+ (snd t)    s = ≈-trans (con-snd (eta-+ t s)) per-+-×2
eta-+ (inl t)    s = ≈-trans (con-inl (eta-+ t s)) hoi-+-+1
eta-+ (inr t)    s = ≈-trans (con-inr (eta-+ t s)) hoi-+-+2
eta-+ (match t u u') s = ≈-trans (con-match (eta-+ t s) ≈-refl ≈-refl) per-+-+
