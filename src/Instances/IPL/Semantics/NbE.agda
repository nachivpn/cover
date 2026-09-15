{-# OPTIONS --safe --without-K #-}

-- Normalization by Evaluation
module Instances.IPL.Semantics.NbE where

open import HeytingAlgebras

open import Instances.IPL.System
open import Instances.IPL.Semantics.Entailment
import Instances.IPL.Semantics.Interpretation as Interpretation
import Instances.IPL.Semantics.Soundness as Soundness

open import Function using (_∘_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Product
  using (Σ ; ∃ ; ∃₂ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)


data _⊢Ne_ : Ctx → Form → Set
data _⊢Nf_ : Ctx → Form → Set

data _⊢Ne_ where
  hyp   : Var Γ a → Γ ⊢Ne a
  ⇒-E   : Γ ⊢Ne (a ⇒ b) → Γ ⊢Nf a → Γ ⊢Ne b
  ∧-E1  : Γ ⊢Ne (a ∧ b) → Γ ⊢Ne a
  ∧-E2  : Γ ⊢Ne (a ∧ b) → Γ ⊢Ne b

data _⊢Nf_ where
  emb   : Γ ⊢Ne (𝕡 i) → Γ ⊢Nf (𝕡 i)
  ⊤-I   : Γ ⊢Nf ⊤
  ⊥-E   : Γ ⊢Ne ⊥ → Γ ⊢Nf a
  ⇒-I   : (Γ `, a) ⊢Nf b → Γ ⊢Nf (a ⇒ b)
  ∧-I   : Γ ⊢Nf a → Γ ⊢Nf b → Γ ⊢Nf (a ∧ b)
  ∨-I1  : Γ ⊢Nf a → Γ ⊢Nf (a ∨ b)
  ∨-I2  : Γ ⊢Nf b → Γ ⊢Nf (a ∨ b)
  ∨-E   : Γ ⊢Ne (a ∨ b) → (Γ `, a) ⊢Nf c → (Γ `, b) ⊢Nf c → Γ ⊢Nf c

wkNe : Γ ⊑ Γ' → Γ ⊢Ne a → Γ' ⊢Ne a
wkNf : Γ ⊑ Γ' → Γ ⊢Nf a → Γ' ⊢Nf a

wkNe i (hyp x)   = hyp (wkVar i x)
wkNe i (⇒-E n x) = ⇒-E (wkNe i n) (wkNf i x)
wkNe i (∧-E1 n)  = ∧-E1 (wkNe i n)
wkNe i (∧-E2 n)  = ∧-E2 (wkNe i n)

wkNf i (emb x)       = emb (wkNe i x)
wkNf i ⊤-I           = ⊤-I
wkNf i (⊥-E x)       = ⊥-E (wkNe i x)
wkNf i (⇒-I n)       = ⇒-I (wkNf (keep i) n)
wkNf i (∧-I n m)     = ∧-I (wkNf i n) (wkNf i m)
wkNf i (∨-I1 n)      = ∨-I1 (wkNf i n)
wkNf i (∨-I2 n)      = ∨-I2 (wkNf i n)
wkNf i (∨-E n m1 m2) = ∨-E (wkNe i n) (wkNf (keep i) m1) (wkNf (keep i) m2)

embNe : Γ ⊢Ne a → Γ ⊢ a
embNf : Γ ⊢Nf a → Γ ⊢ a

embNe (hyp x)   = hyp x
embNe (⇒-E x n) = ⇒-E (embNe x) (embNf n)
embNe (∧-E1 x)  = ∧-E1 (embNe x)
embNe (∧-E2 x)  = ∧-E2 (embNe x)

embNf (emb x) = embNe x
embNf ⊤-I         = ⊤-I
embNf (⊥-E x)     = ⊥-E (embNe x)
embNf (⇒-I n)     = ⇒-I (embNf n)
embNf (∧-I n m)   = ∧-I (embNf n) (embNf m)
embNf (∨-I1 n)    = ∨-I1 (embNf n)
embNf (∨-I2 n)    = ∨-I2 (embNf n)
embNf (∨-E x n m) = ∨-E (embNe x) (embNf n) (embNf m)

-----------------------
-- Base cover system --
-----------------------

open IPLBaseSystem ⊥ _∨_ _⊢Ne_ wkNe
  renaming (K₊ to K ; ForAllW₊ to ForAllW ; LUSetHA to ℛ)
  
------------------------
-- Model construction --
------------------------

Nf' : Form → USet
Nf' a = uset (_⊢Nf a) wkNf

Ne' : Form → USet
Ne' a = uset (_⊢Ne a) wkNe

emb' : Ne' (𝕡 i) →̇ Nf' (𝕡 i)
emb' .apply = emb

∨-I1' : Nf' a →̇ Nf' (a ∨ b)
∨-I1' .apply = ∨-I1

∨-I2' : Nf' b →̇ Nf' (a ∨ b)
∨-I2' .apply = ∨-I2

Nf₊ : Form → LUSet
Nf₊ a = luset (Nf' a) (run𝒥' {Nf' a} localizeNf)
  where
  localizeNf : (k : K Γ) → ForAllW k (_⊢Nf a) → Γ ⊢Nf a
  localizeNf (leaf _)         h = h here
  localizeNf (dead x)         h = ⊥-E x
  localizeNf (branch x k1 k2) h = ∨-E x (localizeNf k1 (h ∘ left)) (localizeNf k2 (h ∘ right))

open Interpretation ℛ (Nf₊ ∘ 𝕡) -- imports ⟦-⟧
open LUSet -- imports localize and 𝒳

---------------------
-- Residualization --
---------------------

--reify   : ∀ a → ⟦ a ⟧ →̇₊ (Nf₊ a)
-- or equivalently:
reify   : ∀ a → ⟦ a ⟧ .𝒳 →̇ Nf' a
reflect : ∀ a → Ne' a →̇ ⟦ a ⟧ .𝒳

reify (𝕡 i)   = id'
reify ⊤       = fun (λ _ → ⊤-I)
reify (a ⇒ b) = fun λ x → ⇒-I (reify b .apply (x freshWk (reflect a .apply (hyp zero))))
reify (a ∧ b) = fun λ x → ∧-I (reify a .apply (proj₁ x)) (reify b .apply (proj₂ x))
reify ⊥       = Nf₊ ⊥ .localize ∘' 𝒥'-map (⊥'-elim {Nf' ⊥})
reify (a ∨ b) = Nf₊ (a ∨ b) .localize ∘' 𝒥'-map [ ∨-I1' ∘' reify a  , ∨-I2' ∘' reify b ]'

reflect (𝕡 i)   = emb'
reflect ⊤       = unit'
reflect (a ⇒ b) = fun λ n i x → reflect b .apply (⇒-E (wkNe i n) (reify a .apply x))
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

quot : (⟦ Γ ⟧c →̇₊ ⟦ a ⟧) → Γ ⊢Nf a
quot {Γ} {a} f = reify a .apply (f .apply (idEnv Γ))

nbe : Γ ⊢ a → Γ ⊢Nf a
nbe t = let open Soundness.Proof ℛ (Nf₊ ∘ 𝕡) in quot (⟦-⟧-sound t)

completeness : Γ ⊨ₐ a → Γ ⊢ a
completeness f = embNf (quot (f ℛ (Nf₊ ∘ 𝕡)))
