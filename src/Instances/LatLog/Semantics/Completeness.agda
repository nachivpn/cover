{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.Semantics.Completeness where

open import Instances.LatLog.System
open import Instances.LatLog.Semantics.Entailment
import Instances.LatLog.Semantics.Interpretation as Interpretation

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

data K₊ : Ctx → Set where
  leaf    : (Γ : Ctx) → K₊ Γ
  dead    : Γ ⊢ ⊥ → K₊ Γ
  branch  : Γ ⊢ (a ∨ b) → K₊ ([] `, a) → K₊ ([] `, b) → K₊ Γ

data _∈₊_ : Ctx → {Γ : Ctx} → K₊ Γ → Set where
  here : Δ ∈₊ leaf Δ
  left : {n : Γ ⊢ (a ∨ b)} {k : K₊ ([] `, a)} {k' : K₊ ([] `, b)}
    → Δ ∈₊ k → Δ ∈₊ branch n k k'
  right : {n : Γ ⊢ (a ∨ b)} {k : K₊ ([] `, a)} {k' : K₊ ([] `, b)}
    → Δ ∈₊ k' → Δ ∈₊ branch n k k'

open import Neighborhood.Lib 𝕎 K₊ _∈₊_
    renaming (∣_∣ to ∣_∣₊ ; ForAllW to ForAllW₊)
open import Neighborhood.Systems 𝕎

wkK₊ : Γ ⊑ Γ' → K₊ Γ → K₊ Γ'
wkK₊ i (leaf Δ)        = leaf _
wkK₊ i (dead n)        = dead (wkTm i n)
wkK₊ i (branch n k k') = branch (wkTm i n) k k'

wkK₊-ref : (i : Γ ⊑ Γ') (k : K₊ Γ) → ∣ k ∣₊ ≼ ∣ wkK₊ i k ∣₊
wkK₊-ref i (leaf _) here
    = _ , here , i
wkK₊-ref i (dead x) ()
wkK₊-ref i (branch x k1 k2) (left p)
  = (-, left p , ⊑-refl)
wkK₊-ref i (branch x k1 k2) (right p)
  = (-, right p , ⊑-refl)

idK₊ = leaf

idK₊-sub : ∣ idK₊ Γ ∣₊ ⊆ ⟨ Γ ⟩
idK₊-sub here = ≡-refl

transK₊ : (k : K₊ Γ) → ForAllW₊ k K₊ → K₊ Γ
transK₊ (leaf _)        f = f here
transK₊ (dead x)        f = dead x
transK₊ (branch x k k') f = branch x (transK₊ k (f ∘ left)) (transK₊ k' (f ∘ right))

transK₊-sub : (k : K₊ Γ) (h : ForAllW₊ k K₊)
    → ∣ transK₊ k h ∣₊ ⊆ ⨆ ∣ k ∣₊ (∣_∣₊ ∘ h)
transK₊-sub (leaf Γ)        h p
    = (Γ , here) , p
transK₊-sub (dead x)        h ()
transK₊-sub (branch x k k') h (left p)  =
  let (vl , p') , pl = transK₊-sub k (h ∘ left) p
  in (vl , left p') , pl
transK₊-sub (branch x k k') h (right p) =
  let (vl , p') , pr = transK₊-sub k' (h ∘ right) p
  in (vl , right p') , pr

NS : NeighborhoodSystem
NS = record
  { N = K₊ ; _∈_ = _∈₊_
  ; refinement = record { wkN = wkK₊ ; wkN-ref = wkK₊-ref }
  }

LS : LatLogSystem NS
LS = record
  { identity = record
    { idN[_]  = idK₊
    ; idN-sub = idK₊-sub
    }
  ; transitivity = record
    { transN = transK₊
    ; transN-sub = transK₊-sub
    }
  }

open import USet.Base 𝕎
open import USet.Lattice.Localized 𝕎 LS renaming (LUSetBL to ℛ)

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
  localizeTm (leaf x)         h = h here
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
reify (a ∧ b) = fun λ x → ∧-I (reify a .apply (proj₁ x)) (reify b .apply (proj₂ x))
reify ⊥       = Tm₊ ⊥ .localize ∘' map𝒥' (⊥'-elim {Tm' ⊥})
reify (a ∨ b) = Tm₊ (a ∨ b) .localize ∘' map𝒥' [ ∨-I1' ∘' reify a  , ∨-I2' ∘' reify b ]'

reflect (𝕡 i)   = id'
reflect ⊤       = unit'
reflect (a ∧ b) = fun λ n → reflect a .apply (∧-E1 n) , reflect b .apply (∧-E2 n)
reflect ⊥       = fun λ n → dead n , λ {()}
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
