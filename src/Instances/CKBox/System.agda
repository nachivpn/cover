{-# OPTIONS --safe --without-K #-}

-- Dual Context K calculus
module Instances.CKBox.System where

open import Data.Nat using () renaming (ℕ to Atom) public
open import Data.Product using (_×_ ; _,_)

open import PUtil

open import Function

infix  3  _⨾_⊢_

data Form : Set where
  𝕡  : Atom → Form
  ⊤ ⊥ : Form
  _⇒_ _∧_ _∨_ : Form → Form → Form
  ◻_ : Form → Form

variable
  a b c d : Form
  i j : Atom

open import Context Form public

data _⨾_⊢_ (Δ Γ : Ctx) : Form → Set where
  hyp   : (x : Var Γ a) → Δ ⨾ Γ ⊢ a

  -- truth
  ⊤-I   : Δ ⨾ Γ ⊢ ⊤

  -- falsity
  ⊥-E   : Δ ⨾ Γ ⊢ ⊥ → Δ ⨾ Γ ⊢ a

  -- conjunction
  ∧-I   : Δ ⨾ Γ ⊢ a → Δ ⨾ Γ ⊢ b → Δ ⨾ Γ ⊢ (a ∧ b)
  ∧-E1  : Δ ⨾ Γ ⊢ (a ∧ b) → Δ ⨾ Γ ⊢ a
  ∧-E2  : Δ ⨾ Γ ⊢ (a ∧ b) → Δ ⨾ Γ ⊢ b

  -- disjunction
  ∨-I1  : Δ ⨾ Γ ⊢ a → Δ ⨾ Γ ⊢ (a ∨ b)
  ∨-I2  : Δ ⨾ Γ ⊢ b → Δ ⨾ Γ ⊢ (a ∨ b)
  ∨-E   : Δ ⨾ Γ ⊢ (a ∨ b) → Δ ⨾ (Γ `, a) ⊢ c → Δ ⨾  (Γ `, b) ⊢ c → Δ ⨾ Γ ⊢ c

  -- implication
  ⇒-I   : Δ ⨾ (Γ `, a) ⊢ b → Δ ⨾ Γ ⊢ (a ⇒ b)
  ⇒-E   : Δ ⨾ Γ ⊢ (a ⇒ b) → Δ ⨾ Γ ⊢ a → Δ ⨾ Γ ⊢ b

  -- box modality
  ◻-I   : (t : [] ⨾ Δ ⊢ a) →  Δ ⨾ Γ ⊢ (◻ a)
  ◻-E   : (t : Δ ⨾ Γ ⊢ (◻ a)) → (u : (Δ `, a) ⨾ Γ ⊢ b) →  Δ ⨾ Γ ⊢ b

--
-- Meta-properties
--

wkTm : Δ ⊑ Δ' → Γ ⊑ Γ' → Δ ⨾ Γ ⊢ a → Δ' ⨾ Γ' ⊢ a
wkTm i1 i2 (hyp x)       = hyp (wkVar i2 x)
wkTm i1 i2 ⊤-I           = ⊤-I
wkTm i1 i2 (⊥-E t)       = ⊥-E (wkTm i1 i2 t)
wkTm i1 i2 (∧-I t u)     = ∧-I (wkTm i1 i2 t) (wkTm i1 i2 u)
wkTm i1 i2 (∧-E1 t)      = ∧-E1 (wkTm i1 i2 t)
wkTm i1 i2 (∧-E2 t)      = ∧-E2 (wkTm i1 i2 t)
wkTm i1 i2 (∨-I1 t)      = ∨-I1 (wkTm i1 i2 t)
wkTm i1 i2 (∨-I2 t)      = ∨-I2 (wkTm i1 i2 t)
wkTm i1 i2 (∨-E t u1 u2) = ∨-E (wkTm i1 i2 t) (wkTm i1 (keep i2) u1) (wkTm i1 (keep i2) u2)
wkTm i1 i2 (⇒-I t)       = ⇒-I (wkTm i1 (keep i2) t)
wkTm i1 i2 (⇒-E t u)     = ⇒-E (wkTm i1 i2 t) (wkTm i1 i2 u)
wkTm i1 i2 (◻-I t)       = ◻-I (wkTm base i1 t)
wkTm i1 i2 (◻-E t u)     = ◻-E (wkTm i1 i2 t) (wkTm (keep i1) i2 u)

--
-- Dual contexts
--

Ctx₂ : Set
Ctx₂ = Ctx × Ctx

variable
  Χ Χ' Χ'' Χ''' : Ctx₂

_⊑₂_ : Ctx × Ctx → Ctx × Ctx → Set
(Δ , Γ) ⊑₂ (Δ' , Γ') = Δ ⊑ Δ' × Γ ⊑ Γ'

⊑₂-trans : Χ ⊑₂ Χ' → Χ' ⊑₂ Χ'' → Χ ⊑₂ Χ''
⊑₂-trans (i1 , i2) (i1' , i2') = ⊑-trans i1 i1' , ⊑-trans i2 i2'

⊑₂-refl : Χ ⊑₂ Χ
⊑₂-refl = ⊑-refl , ⊑-refl

freshWkL₂ : (Δ , Γ) ⊑₂ ((Δ `, a), Γ)
freshWkL₂ = freshWk , ⊑-refl

freshWkR₂ : (Δ , Γ) ⊑₂ (Δ , (Γ `, a))
freshWkR₂ = ⊑-refl , freshWk

open import Frame.IFrame

𝕎₂ : Preorder Ctx₂ _⊑₂_
𝕎₂ = record
      { ⊑-trans = ⊑₂-trans
      ; ⊑-refl  = ⊑₂-refl
      }
