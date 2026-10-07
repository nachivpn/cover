{-# OPTIONS --safe --without-K #-}

module Instances.CBPV.System where

open import Data.Nat using () renaming (ℕ to Atom) public

data Tyᵛ : Set -- Value (~ "positive") types
data Tyᶜ : Set -- Computation (~ "negative") types

data Tyᵛ where
  𝕡ᵛ  : Atom → Tyᵛ
  
  -- positive ("pattern-matching") products
  𝟙ᵛ   : Tyᵛ
  _×ᵛ_ : Tyᵛ → Tyᵛ → Tyᵛ

  -- sums
  𝟘    : Tyᵛ
  _＋_ : Tyᵛ → Tyᵛ → Tyᵛ

  -- thunks
  𝕌   : Tyᶜ → Tyᵛ
  
data Tyᶜ where
  𝕡ᶜ  : Atom → Tyᶜ

  -- negative ("projecting") products
  𝟙ᶜ   : Tyᶜ
  _×ᶜ_ : Tyᶜ → Tyᶜ → Tyᶜ

  -- implication
  _⇒_ : Tyᵛ → Tyᶜ → Tyᶜ

  -- value-computations
  𝔽   : Tyᵛ → Tyᶜ

variable
  A A' A₁ A₁' A₂ A₂' A₃ A₃' : Tyᵛ
  B B' B₁ B₁' B₂ B₂' B₃ B₃' : Tyᶜ
  i j : Atom

-- Context is a list of positive formulAs
-- (intuition: substitution is a list of 'values')
open import Context Tyᵛ public

--
-- Syntax
--

infix 6 _⊢ᵛ_ _⊢ᶜ_
data _⊢ᵛ_ : Ctx → Tyᵛ → Set
data _⊢ᶜ_ : Ctx → Tyᶜ → Set

data _⊢ᵛ_ where

  -- variables
  var    : Var Γ A → Γ ⊢ᵛ A
  
  -- positive unit and products
  unitᵛ  : Γ ⊢ᵛ 𝟙ᵛ
  pairᵛ  : Γ ⊢ᵛ A₁ → Γ ⊢ᵛ A₂ → Γ ⊢ᵛ A₁ ×ᵛ A₂

  -- sums
  inl    : Γ ⊢ᵛ A₁ → Γ ⊢ᵛ A₁ ＋ A₂
  inr    : Γ ⊢ᵛ A₁ → Γ ⊢ᵛ A₁ ＋ A₂

  -- thunks
  thunk  : Γ ⊢ᶜ B → Γ ⊢ᵛ 𝕌 B

data _⊢ᶜ_ where

  -- negative products
  unitᶜ  : Γ ⊢ᶜ 𝟙ᶜ
  pairᶜ  : Γ ⊢ᶜ B₁ → Γ ⊢ᶜ B₂ → Γ ⊢ᶜ B₁ ×ᶜ B₂
  fst    : Γ ⊢ᶜ B₁ ×ᶜ B₂ → Γ ⊢ᶜ B₁
  snd    : Γ ⊢ᶜ B₁ ×ᶜ B₂ → Γ ⊢ᶜ B₂

  -- implication
  lam    : Γ `, A ⊢ᶜ B → Γ ⊢ᶜ A ⇒ B
  app    : Γ ⊢ᶜ A ⇒ B → Γ ⊢ᵛ A → Γ ⊢ᶜ B

  -- computations
  return : Γ ⊢ᵛ A → Γ ⊢ᶜ 𝔽 A
  bind   : Γ ⊢ᶜ 𝔽 A → Γ `, A ⊢ᶜ B → Γ ⊢ᶜ B

  -- value eliminators
  split : Γ ⊢ᵛ A₁ ×ᵛ A₂ → (Γ `, A₁ `, A₂) ⊢ᶜ B → Γ ⊢ᶜ B
  abort : Γ ⊢ᵛ 𝟘 → Γ ⊢ᶜ B
  case  : Γ ⊢ᵛ A₁ ×ᵛ A₂ → Γ `, A₂ ⊢ᶜ B → Γ `, A₂ ⊢ᶜ B → Γ ⊢ᶜ B
  force : Γ ⊢ᵛ 𝕌 B → Γ ⊢ᶜ B
  
wkTmᵛ : Γ ⊑ Γ' → Γ ⊢ᵛ A → Γ' ⊢ᵛ A
wkTmᶜ : Γ ⊑ Γ' → Γ ⊢ᶜ B → Γ' ⊢ᶜ B

wkTmᵛ i (var x)     = var (wkVar i x)
wkTmᵛ i unitᵛ       = unitᵛ
wkTmᵛ i (pairᵛ t u) = pairᵛ (wkTmᵛ i t) (wkTmᵛ i u)
wkTmᵛ i (inl t)     = inl (wkTmᵛ i t)
wkTmᵛ i (inr t)     = inr (wkTmᵛ i t)
wkTmᵛ i (thunk t)   = thunk (wkTmᶜ i t)

wkTmᶜ i unitᶜ        = unitᶜ
wkTmᶜ i (pairᶜ t u)  = pairᶜ (wkTmᶜ i t) (wkTmᶜ i u)
wkTmᶜ i (fst t)      = fst (wkTmᶜ i t)
wkTmᶜ i (snd t)      = snd (wkTmᶜ i t)
wkTmᶜ i (lam t)      = lam (wkTmᶜ (keep i) t)
wkTmᶜ i (app t v)    = app (wkTmᶜ i t) (wkTmᵛ i v)
wkTmᶜ i (return v)   = return (wkTmᵛ i v)
wkTmᶜ i (bind t u)   = bind (wkTmᶜ i t) (wkTmᶜ (keep i) u)
wkTmᶜ i (split v t)  = split (wkTmᵛ i v) (wkTmᶜ (keep (keep i)) t)
wkTmᶜ i (abort v)    = abort (wkTmᵛ i v)
wkTmᶜ i (case v t u) = case (wkTmᵛ i v) (wkTmᶜ (keep i) t) (wkTmᶜ (keep i) u)
wkTmᶜ i (force v)    = force (wkTmᵛ i v)
