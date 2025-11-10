{-# OPTIONS --safe #-}

module Instances.Wish.PLL where

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)

open import PUtil

open import Function
open import Data.Sum

data Form : Set where
  𝕡 ⊥         : Form
  _⇒_ _∧_ _∨_ : Form → Form → Form
  ○           : Form → Form

private
  variable
    a b c d : Form

open import Context Form

--
-- Syntax
--

data _⊢_ : Ctx → Form → Set where

  -- hypothesis
  hyp   : Var Γ a → Γ ⊢ a

  -- implication
  ⇒-I   : (Γ `, a) ⊢ b → Γ ⊢ (a ⇒ b)
  ⇒-E   : Γ ⊢ (a ⇒ b) → Γ ⊢ a → Γ ⊢ b

  -- conjunction
  ∧-I   : Γ ⊢ a → Γ ⊢ b → Γ ⊢ (a ∧ b)
  ∧-E1  : Γ ⊢ (a ∧ b) → Γ ⊢ a
  ∧-E2  : Γ ⊢ (a ∧ b) → Γ ⊢ b

  -- disjunction
  ∨-I1  : Γ ⊢ a → Γ ⊢ (a ∨ b)
  ∨-I2  : Γ ⊢ b → Γ ⊢ (a ∨ b)
  ∨-E   : Γ ⊢ (a ∨ b) → (Γ `, a) ⊢ c → (Γ `, a) ⊢ c → Γ ⊢ c

  -- modality
  ○-I   : Γ ⊢ a → Γ ⊢ (○ a)
  ○-E   : Γ ⊢ (○ a) → (Γ `, a) ⊢ (○ b) → Γ ⊢ (○ b)

data _⊢Ne_ : Ctx → Form → Set
data _⊢Nf_ : Ctx → Form → Set

data _⊢Ne_ where
  hyp   : Var Γ a → Γ ⊢Ne a
  ⇒-E   : Γ ⊢Ne (a ⇒ b) → Γ ⊢Nf a → Γ ⊢Ne b
  ∧-E1  : Γ ⊢Ne (a ∧ b) → Γ ⊢Ne a
  ∧-E2  : Γ ⊢Ne (a ∧ b) → Γ ⊢Ne b

data _⊢Nf_ where
  emb   : Γ ⊢Ne 𝕡 → Γ ⊢Nf 𝕡
  ⇒-I   : (Γ `, a) ⊢Nf b → Γ ⊢Nf (a ⇒ b)
  ∧-I   : Γ ⊢Nf a → Γ ⊢Nf b → Γ ⊢Nf (a ∧ b)
  ∨-I1  : Γ ⊢Nf a → Γ ⊢Nf (a ∨ b)
  ∨-I2  : Γ ⊢Nf b → Γ ⊢Nf (a ∨ b)
  ∨-E   : Γ ⊢Ne (a ∨ b) → (Γ `, a) ⊢Nf c → (Γ `, a) ⊢Nf c → Γ ⊢Nf c
  ○-I   : Γ ⊢Nf a → Γ ⊢Nf (○ a)
  ○-E   : Γ ⊢Ne (○ a) → (Γ `, a) ⊢Nf b → Γ ⊢Nf (○ b)

wkNe : Γ ⊆ Γ' → Γ ⊢Ne a → Γ' ⊢Ne a
wkNf : Γ ⊆ Γ' → Γ ⊢Nf a → Γ' ⊢Nf a

wkNe i (hyp x)   = hyp (wkVar i x)
wkNe i (⇒-E n x) = ⇒-E (wkNe i n) (wkNf i x)
wkNe i (∧-E1 n)  = ∧-E1 (wkNe i n)
wkNe i (∧-E2 n)  = ∧-E2 (wkNe i n)

wkNf i (emb x)       = emb (wkNe i x)
wkNf i (⇒-I n)       = ⇒-I (wkNf (keep i) n)
wkNf i (∧-I n m)     = ∧-I (wkNf i n) (wkNf i m)
wkNf i (∨-I1 n)      = ∨-I1 (wkNf i n)
wkNf i (∨-I2 n)      = ∨-I2 (wkNf i n)
wkNf i (∨-E n m1 m2) = ∨-E (wkNe i n) (wkNf (keep i) m1) (wkNf (keep i) m2)
wkNf i (○-I n)       = ○-I (wkNf i n)
wkNf i (○-E n m)     = ○-E (wkNe i n) (wkNf (keep i) m)


  
