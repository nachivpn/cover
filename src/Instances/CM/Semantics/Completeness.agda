{-# OPTIONS --safe --without-K #-}

module Instances.CM.Semantics.Completeness where

open import Instances.CM.System
open import Instances.CM.Semantics.Entailment
import Instances.CM.Semantics.Interpretation as Interpretation

open import Neighborhood.Systems 𝕎

open import Function using (_∘_)
open import Data.Empty renaming (⊥ to ⊥′ ; ⊥-elim to ⊥′-elim)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Product
  using (Σ ; ∃ ; ∃₂ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)

-----------------------
-- Base cover system --
-----------------------

open IPLBaseSystem ⊥ _∨_ _⊢_ wkTm

-----------------------
-- ⋆ modality system --
-----------------------

data K⋆ : Ctx → Set where
  single  : Γ ⊢ ⋆ a → K⋆ Γ
  dead    : Γ ⊢ ⊥ → K⋆ Γ
  branch  : Γ ⊢ (a ∨ b) → K⋆ (Γ `, a) → K⋆ (Γ `, b) → K⋆ Γ

data _∈⋆_  : Ctx → {Γ : Ctx} → K⋆ Γ → Set where
  here  : {n : Γ ⊢ ⋆ a} → ([] `, a) ∈⋆ single n
  left  : {n : Γ ⊢ (a ∨ b)} {k : K⋆ (Γ `, a)} {k' : K⋆ (Γ `, b)}
    → Δ ∈⋆ k → Δ ∈⋆ branch n k k'
  right : {n : Γ ⊢ (a ∨ b)} {k : K⋆ (Γ `, a)} {k' : K⋆ (Γ `, b)}
    → Δ ∈⋆ k' → Δ ∈⋆ branch n k k'

open import Neighborhood.Lib 𝕎 K⋆ _∈⋆_ using () 
  renaming (∣_∣ to ∣_∣⋆ ; ForAllW to ForAllW⋆)

wkK⋆ : Γ ⊑ Γ' → K⋆ Γ → K⋆ Γ'
wkK⋆ i (single n)      = single (wkTm i n)
wkK⋆ i (dead n)        = dead (wkTm i n)
wkK⋆ i (branch n k k') = branch (wkTm i n) (wkK⋆ (keep i) k) (wkK⋆ (keep i) k')

wkK⋆-ref : (i : Γ ⊑ Γ') (k : K⋆ Γ) → ∣ k ∣⋆ ≼ ∣ wkK⋆ i k ∣⋆
wkK⋆-ref i (single n) here
  = (-, here , ⊑-refl)
wkK⋆-ref i (dead x) ()
wkK⋆-ref i (branch x k1 k2) (left p)
  = let (Δ , p' , i') = wkK⋆-ref (keep i) k1 p in
     (Δ , left p' , i')
wkK⋆-ref i (branch x k1 k2) (right p)
  = let (Δ , p' , i') = wkK⋆-ref (keep i) k2 p in
     (Δ , right p' , i')

NS⋆ : NeighborhoodSystem
NS⋆ = record
  { N          = K⋆
  ; _∈_        = _∈⋆_
  ; refinement = record { wkN = wkK⋆ ; wkN-ref = wkK⋆-ref }
  }  
  
-- imports ⋆', etc.
open import USet.Mon.CM.Cover 𝕎 NS⋆

------------------------
-- Modal Localization --
------------------------

transK₊⋆ : (k : K₊ Γ) → ForAllW₊ k K⋆ → K⋆ Γ
transK₊⋆ (leaf _)         f = f here
transK₊⋆ (dead x)         f = dead x
transK₊⋆ (branch x k1 k2) f = branch x
  (transK₊⋆ k1 (f ∘ left))
  (transK₊⋆ k2 (f ∘ right))

transK₊⋆-bwd-member : (k : K₊ Γ) (h : ForAllW₊ k K⋆)
  → ∣ transK₊⋆ k h ∣⋆ ⊆ ⨆ ∣ k ∣₊ (∣_∣⋆ ∘ h)
transK₊⋆-bwd-member (leaf Γ)       f p
  = (Γ , here) , p
transK₊⋆-bwd-member (branch x k1 k2) f (left p)
  = let ((Χ , p) , q) = transK₊⋆-bwd-member k1 (f ∘ left) p
    in (Χ , left p) , q
transK₊⋆-bwd-member (branch x k1 k2) f (right p)
  = let ((Χ , p) , q) = transK₊⋆-bwd-member k2 (f ∘ right) p
    in (Χ , right p) , q

⋆'-localize-imm : {A : USet} → 𝒥' (⋆' A) →̇ ⋆' A
⋆'-localize-imm .apply (k , fam) = transK₊⋆ k (proj₁ ∘ fam) , λ x →
  let (x , y) , z = transK₊⋆-bwd-member k (proj₁ ∘ fam) x in (proj₂ ∘ fam) y z

⋆'-localize : {A : USet} → 𝒥' (⋆' A) →̇ ⋆' (𝒥' A)
⋆'-localize {A} = ⋆'-map {A} {𝒥' A} 𝒥'-point ∘' ⋆'-localize-imm {A}

open LocalizedCover WCS₊ (λ {A} → ⋆'-localize {A}) renaming (LUSetCMA to ℛ)

------------------------
-- Model construction --
------------------------

Tm' : Form → USet
Tm' a = uset (_⊢ a) wkTm

∨-I1' : Tm' a →̇ Tm' (a ∨ b)
∨-I1' .apply = ∨-I1

∨-I2' : Tm' b →̇ Tm' (a ∨ b)
∨-I2' .apply = ∨-I2

-- term valuation
Tm₊ : Form → LUSet
Tm₊ a = luset (Tm' a) (run𝒥' {Tm' a} localizeTm)
  where
  localizeTm : (k : K₊ Γ) → ForAllW₊ k (_⊢ a) → Γ ⊢ a
  localizeTm (leaf _)         h = h here
  localizeTm (dead x)         h = ⊥-E x
  localizeTm (branch x k1 k2) h = ∨-E x (localizeTm k1 (h ∘ left)) (localizeTm k2 (h ∘ right))

open Interpretation ℛ (Tm₊ ∘ 𝕡) using (⟦_⟧ ; ⟦_⟧c)
open LUSet -- imports localize and 𝒳

---------------------
-- Residualization --
---------------------

⋆'-collect : ⋆' (Tm' a) →̇ Tm' (⋆ a)
⋆'-collect {a = a} = ⋆'-run {Tm' a} collectAux
  where
  collectAux : (k : K⋆ Γ) (f : ForAllW⋆ k (Tm' a ₀_)) → Tm' (⋆ a) ₀ Γ
  collectAux (dead x)        f = ⊥-E x
  collectAux (single x)      f = ⋆-M x (f here)
  collectAux (branch x k k') f = ∨-E x (collectAux k (f ∘ left)) (collectAux k' (f ∘ right))

⋆'-register : Tm' (⋆ a) →̇ ⋆' (Tm' a)
⋆'-register {a} .apply {Γ} n = single n , λ { here → hyp zero }

reify   : ∀ a → ⟦ a ⟧ →̇₊ (Tm₊ a)
reflect : ∀ a → Tm₊ a →̇₊ ⟦ a ⟧

reify (𝕡 i)   = id'
reify ⊤       = fun (λ _ → ⊤-I)
reify (a ⇒ b) = fun λ x → ⇒-I (reify b .apply (x freshWk (reflect a .apply (hyp zero))))
reify (a ∧ b) = fun λ x → ∧-I (reify a .apply (proj₁ x)) (reify b .apply (proj₂ x))
reify ⊥       = Tm₊ ⊥ .localize ∘' map𝒥' (⊥'-elim {Tm' ⊥})
reify (a ∨ b) = Tm₊ (a ∨ b) .localize ∘' map𝒥' [ ∨-I1' ∘' reify a  , ∨-I2' ∘' reify b ]'
reify (⋆ a)   = ⋆'-collect ∘' ⋆'-map (reify a)

reflect (𝕡 i)   = id'
reflect ⊤       = unit'
reflect (a ⇒ b) = fun λ n i x → reflect b .apply (⇒-E (wkTm i n) (reify a .apply x))
reflect (a ∧ b) = fun λ n → reflect a .apply (∧-E1 n) , reflect b .apply (∧-E2 n)
reflect ⊥       = fun λ n → dead n , λ{()}
reflect (a ∨ b) = fun λ n → branch n (leaf (_ `, a)) (leaf (_ `, b)) ,
  λ { (left here)  → inj₁ (reflect a .apply (hyp zero))
    ; (right here) → inj₂ (reflect b .apply (hyp zero))
    }
reflect (⋆ a)   = ⋆'-map (reflect a) ∘' ⋆'-register

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

------------------
-- Observations --
------------------

private
  obs : ⋆' ⊥' →̇ 𝒥' ⊥'
  obs .apply (k , p) = dead (aux k p) , λ { () }
    where
    aux : (k : K⋆ Γ) → (∀ {v} → v ∈⋆ k → ⊥′) → Γ ⊢ ⊥
    aux (single x)       p = ⊥′-elim (p here)
    aux (dead x)         p = x
    aux (branch x k1 k2) p = ∨-E x (aux k1 (p ∘ left)) (aux k2 (p ∘ right))

