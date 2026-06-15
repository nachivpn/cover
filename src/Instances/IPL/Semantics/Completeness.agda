{-# OPTIONS --safe --without-K #-}

module Instances.IPL.Semantics.Completeness where

open import Instances.IPL.System
open import Instances.IPL.Semantics.Entailment
import Instances.IPL.Semantics.Interpretation as Interpretation

open import Function using (_∘_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Product
  using (Σ ; ∃ ; ∃₂ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)

-----------------------
-- Base cover system --
-----------------------

open IPLBaseSystem ⊥ _∨_ _⊢_ wkTm renaming (LUSetHA to ℛ)

------------------------
-- Model construction --
------------------------

Tm' : Form → USet
Tm' a = uset (_⊢ a) wkTm

∨-I1' : Tm' a →̇ Tm' (a ∨ b)
∨-I1' .apply = ∨-I1

∨-I2' : Tm' b →̇ Tm' (a ∨ b)
∨-I2' .apply = ∨-I2

Tm₊ : Form → LUSet
Tm₊ a = luset (Tm' a) (run𝒥' {Tm' a} localizeTm)
  where
  localizeTm : (k : K₊ Γ) → ForAllW₊ k (_⊢ a) → Γ ⊢ a
  localizeTm (leaf _)         h = h here
  localizeTm (dead x)         h = ⊥-E x
  localizeTm (branch x k1 k2) h = ∨-E x (localizeTm k1 (h ∘ left)) (localizeTm k2 (h ∘ right))

open Interpretation ℛ (Tm₊ ∘ 𝕡) -- imports ⟦-⟧
open LUSet -- imports localize and 𝒳

---------------------
-- Residualization --
---------------------

--reify   : ∀ a → ⟦ a ⟧ →̇₊ (Tm₊ a)
-- or equivalently:
reify   : ∀ a → ⟦ a ⟧ .𝒳 →̇ Tm' a
reflect : ∀ a → Tm' a →̇ ⟦ a ⟧ .𝒳

reify (𝕡 i)   = id'
reify ⊤       = fun (λ _ → ⊤-I)
reify (a ⇒ b) = fun λ x → ⇒-I (reify b .apply (x freshWk (reflect a .apply (hyp zero))))
reify (a ∧ b) = fun λ x → ∧-I (reify a .apply (proj₁ x)) (reify b .apply (proj₂ x))
reify ⊥       = Tm₊ ⊥ .localize ∘' map𝒥' (⊥'-elim {Tm' ⊥})
reify (a ∨ b) = Tm₊ (a ∨ b) .localize ∘' map𝒥' [ ∨-I1' ∘' reify a  , ∨-I2' ∘' reify b ]'

reflect (𝕡 i)   = id'
reflect ⊤       = unit'
reflect (a ⇒ b) = fun λ n i x → reflect b .apply (⇒-E (wkTm i n) (reify a .apply x))
reflect (a ∧ b) = fun λ n → reflect a .apply (∧-E1 n) , reflect b .apply (∧-E2 n)
reflect ⊥       = fun λ n → dead n , λ{()}
reflect (a ∨ b) = fun λ n → branch n (leaf (_ `, a)) (leaf (_ `, b)) ,
  λ { (left here)  → inj₁ (reflect a .apply (hyp zero))
    ; (right here) → inj₂ (reflect b .apply (hyp zero))
    }

------------------
-- Completeness --
------------------

idEnv : ∀ Γ → ⟦ Γ ⟧c .𝒳 ₀ Γ
idEnv []       = _
idEnv (Γ `, a) = wk (⟦ Γ ⟧c .𝒳) freshWk (idEnv Γ) , reflect a .apply (hyp zero)

quot : (⟦ Γ ⟧c →̇₊ ⟦ a ⟧) → Γ ⊢ a
quot {Γ} {a} f = reify a .apply (f .apply (idEnv Γ))

completeness : Γ ⊨ₐ a → Γ ⊢ a
completeness f = quot (f ℛ (Tm₊ ∘ 𝕡))
