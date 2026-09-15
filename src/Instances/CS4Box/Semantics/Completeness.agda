{-# OPTIONS --safe --without-K #-}

module Instances.CS4Box.Semantics.Completeness where

open import Instances.CS4Box.System
open import Instances.CS4Box.Semantics.Entailment

open import Neighborhood.Systems 𝕎₂

open import Function using (_∘_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product
  using (Σ; ∃; ∃₂; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl)

-----------------------
-- Base cover system --
-----------------------

data K₊ : Ctx → Ctx → Set where
  leaf    : (Δ Γ : Ctx) → K₊ Δ Γ
  dead    : Δ ⨾ Γ ⊢ ⊥ → K₊ Δ Γ
  cons    : Δ ⨾ Γ ⊢ (◻ a) → K₊ (Δ `, a) Γ → K₊ Δ Γ
  branch  : Δ ⨾ Γ ⊢ (a ∨ b) → K₊ Δ (Γ `, a) → K₊ Δ (Γ `, b) → K₊ Δ Γ

data _⨾_∈₊_ : Ctx →  Ctx → K₊ Δ Γ → Set where
  here : Δ ⨾ Γ ∈₊ leaf Δ Γ
  there : {n : Δ ⨾ Γ ⊢ (◻ a)} {k : K₊ (Δ `, a) Γ}
        → Ξ ⨾ Θ ∈₊ k → Ξ ⨾ Θ ∈₊ cons n k
  left : {n : Δ ⨾ Γ ⊢ (a ∨ b)} {k : K₊ Δ (Γ `, a)} {k' : K₊ Δ (Γ `, b)}
    → Ξ ⨾ Θ ∈₊ k → Ξ ⨾ Θ ∈₊ branch n k k'
  right : {n : Δ ⨾ Γ ⊢ (a ∨ b)} {k : K₊ Δ (Γ `, a)} {k' : K₊ Δ (Γ `, b)}
    → Ξ ⨾ Θ ∈₊ k' → Ξ ⨾ Θ ∈₊ branch n k k'

K₊₂ = uncurry K₊

wkK₊ : Δ ⊑ Δ' → Γ ⊑ Γ' → K₊ Δ Γ → K₊ Δ' Γ'
wkK₊ i1 i2 (leaf _ _)       = leaf _ _
wkK₊ i1 i2 (dead x)         = dead (wkTm i1 i2 x)
wkK₊ i1 i2 (cons x k)       = cons (wkTm i1 i2 x) (wkK₊ (keep i1) i2 k)
wkK₊ i1 i2 (branch x k1 k2) = branch (wkTm i1 i2 x) (wkK₊ i1 (keep i2) k1) (wkK₊ i1 (keep i2) k2)

wkK₊₂ : Χ ⊑₂ Χ' → K₊₂ Χ → K₊₂ Χ'
wkK₊₂ = uncurry wkK₊

_∈₊_ : Ctx₂ → ∀ {Χ} → K₊₂ Χ → Set
Χ ∈₊ k = uncurry (_⨾_∈₊ k) Χ

open import Neighborhood.Lib 𝕎₂ K₊₂ _∈₊_
  renaming (∣_∣ to ∣_∣₊ ; ForAllW to ForAllW₊)

wkK₊-ref : (i1 : Δ ⊑ Δ') (i2 : Γ ⊑ Γ') (k : K₊ Δ Γ)
  → ∣ k ∣₊ ≼ ∣ wkK₊ i1 i2 k ∣₊
wkK₊-ref i1 i2 (leaf _ _) here
  = _ , here , i1 , i2
wkK₊-ref i1 i2 (dead x) ()
wkK₊-ref i1 i2 (cons x k) (there p)
  = let (Δ , p' , i') = wkK₊-ref (keep i1) i2 k p in
     (Δ , there p' , i')
wkK₊-ref i1 i2 (branch x k1 k2) (left p)
  = let (Δ , p' , i') = wkK₊-ref i1 (keep i2) k1 p in
     (Δ , left p' , i')
wkK₊-ref i1 i2 (branch x k1 k2) (right p)
  = let (Δ , p' , i') = wkK₊-ref i1 (keep i2) k2 p in
     (Δ , right p' , i')

wkK₊₂-ref : (i : Χ ⊑₂ Χ') (k : K₊₂ Χ) → ∣ k ∣₊ ≼ ∣ wkK₊₂ i k ∣₊
wkK₊₂-ref = uncurry wkK₊-ref

K₊-ref : (k : K₊ Δ Γ) → ForAllW₊ k ((Δ , Γ) ⊑₂_)
K₊-ref (leaf _ _)         here
  = ⊑₂-refl
K₊-ref (dead x)         ()
K₊-ref (cons x k) (there p)
  = ⊑₂-trans freshWkL₂ (K₊-ref k p)
K₊-ref (branch x k1 k2) (left p)
  = ⊑₂-trans freshWkR₂ (K₊-ref k1 p)
K₊-ref (branch x k1 k2) (right p)
  = ⊑₂-trans freshWkR₂ (K₊-ref k2 p)

idK₊ = leaf

idK₊-sub : ∣ idK₊ Δ Γ ∣₊ ⊆ ⟨ Δ , Γ ⟩
idK₊-sub here = ≡-refl

transK₊ : (k : K₊ Δ Γ) → ForAllW₊ k K₊₂ → K₊ Δ Γ
transK₊ (leaf _ _)      f = f here
transK₊ (dead x)        f = dead x
transK₊ (cons x k)      f = cons x (transK₊ k (f ∘ there))
transK₊ (branch x k k') f = branch x (transK₊ k (f ∘ left)) (transK₊ k' (f ∘ right))

transK₊-sub : (k : K₊ Δ Γ) (h : ForAllW₊ k K₊₂)
  → ∣ transK₊ k h ∣₊ ⊆ ⨆ ∣ k ∣₊ (∣_∣₊ ∘ h)
transK₊-sub (leaf Δ Γ)      h p
  = ((Δ , Γ) , here) , p
transK₊-sub (dead x)        h ()
transK₊-sub (cons x k) h (there p)
  = let ((v , p') , pr) = transK₊-sub k (h ∘ there) p
    in (v , there p') , pr
transK₊-sub (branch x k k') h (left p)
  = let ((vl , p') , pl) = transK₊-sub k (h ∘ left) p
    in (vl , left p') , pl
transK₊-sub (branch x k k') h (right p)
  = let ((vl , p') , pr) = transK₊-sub k' (h ∘ right) p
    in (vl , right p') , pr

NS₊ : NeighborhoodSystem
NS₊ = record
  { N          = K₊₂
  ; _∈_        = _∈₊_
  ; refinement = record { wkN = wkK₊₂ ; wkN-ref = wkK₊₂-ref }
  }

CS₊ : CoverSystem NS₊
CS₊ = record
  { inclusion    = record { N-ref = K₊-ref }
  ; identity     = record { idN[_] = uncurry idK₊ ; idN-sub = idK₊-sub }
  ; transitivity = record { transN = transK₊ ; transN-sub = transK₊-sub }
  }

WCS₊ : WeakCoverSystem NS₊
WCS₊ = CoverSystem.weakCoverSystem CS₊

open import USet.Base 𝕎₂
open import USet.Localized 𝕎₂ WCS₊

-----------------------
-- ◻ modality system --
-----------------------

data K◻ : Ctx → Ctx → Set where
  single : (Δ : Ctx) (Γ : Ctx) → K◻ Δ Γ

data _⨾_∈◻_ : Ctx → Ctx → K◻ Δ Γ → Set where
  here  : Ξ ⨾ [] ∈◻ single Ξ Θ

wkK◻ : Δ ⊑ Δ' → Γ ⊑ Γ' → K◻ Δ Γ → K◻ Δ' Γ'
wkK◻ i1 i2 (single _ _) = single _ _

K◻₂ = uncurry K◻

wkK◻₂ : Χ ⊑₂ Χ' → K◻₂ Χ → K◻₂ Χ'
wkK◻₂ = uncurry wkK◻

_∈◻_ : Ctx₂ → ∀ {Χ} → K◻₂ Χ → Set
Χ ∈◻ k = uncurry (_⨾_∈◻ k) Χ

open import Neighborhood.Lib 𝕎₂ K◻₂ _∈◻_ using ()
  renaming (∣_∣ to ∣_∣◻ ; ForAllW to ForAllW◻ ; ExistsW to ExistsW◻ ; ⟨_⟩ to ⟨_⟩◻)

wkK◻-ref : (i1 : Δ ⊑ Δ') (i2 : Γ ⊑ Γ') (k : K◻ Δ Γ)
  → ∣ k ∣◻ ≼ ∣ wkK◻ i1 i2 k ∣◻
wkK◻-ref i1 i2 (single _ _) here
  = _ , here , i1 , base

wkK◻₂-ref₂ : (i : Χ ⊑₂ Χ') (k : K◻₂ Χ) → ∣ k ∣◻ ≼ ∣ wkK◻₂ i k ∣◻
wkK◻₂-ref₂ = uncurry wkK◻-ref

_⊗_ : K◻ Δ Γ → K◻ Δ Γ → K◻ Δ Γ
single Δ Γ ⊗ k' = k'

∈-bwd-reachable : (k : K◻ Δ Γ) → Ξ ⨾ Θ ∈◻ k → Δ ⊑ Ξ
∈-bwd-reachable (single Δ Γ) here = ⊑-refl[ Δ ]

∈-bwd-reachable₂ : (k : K◻ Δ Γ) → Ξ ⨾ Θ ∈◻ k → (Δ , [])  ⊑₂ (Ξ , Θ)
∈-bwd-reachable₂ k p = ∈-bwd-reachable k p , ⊑-init[ _ ]

⊗-ref₁ : (k1 k2 : K◻ Δ Γ) → ∣ k1 ∣◻ ≼ ∣ k1 ⊗ k2 ∣◻
⊗-ref₁ (single Δ Γ) k2 {Ξ , Θ} p
  = (Δ , []) , here , ∈-bwd-reachable₂ k2 p

⊗-ref₂ : (k1 k2 : K◻ Δ Γ) → ∣ k2 ∣◻ ≼ ∣ k1 ⊗ k2 ∣◻
⊗-ref₂ (single _ _) k2 {Ξ , Θ} p
  = (Ξ , Θ) , p , ⊑₂-refl

unitK◻ : ∀ Χ → K◻₂ Χ
unitK◻ Χ = single _ _

dupK◻ : (k : K◻ Δ Γ) → ForAllW◻ k K◻₂
dupK◻ (single Δ Γ) here = single Δ []

dupK◻-ref : {k : K◻ Δ Γ} (p : Ξ ⨾ Θ ∈◻ k) → ∣ dupK◻ k p ∣◻ ⊆ ↑ (Ξ , Θ)
dupK◻-ref here here = ⊑-refl , base

extK◻-ref : (k : K◻ Δ Γ) → ExistsW◻ k (↓ (Δ , Γ))
extK◻-ref (single Δ Γ) = (Δ , []) , (here , ⊑-refl[ Δ ] , ⊑-init[ Γ ])

NS◻ : NeighborhoodSystem
NS◻ = record
  { N          = K◻₂
  ; _∈_        = _∈◻_
  ; refinement = record { wkN = wkK◻₂ ; wkN-ref = wkK◻₂-ref₂ }
  }

CKBMS : CKBoxModalSystem NS◻
CKBMS = record
  { intclosed = record
    { _⊗_   = _⊗_
    ; ⊗-ref = λ k1 k2 → ⊗-ref₁ k1 k2 , ⊗-ref₂ k1 k2
    }
  ; seriality = record { unitN[_] = unitK◻ }
  }
  
CS4BMS : CS4BoxModalSystem NS◻
CS4BMS = record
  { ckBoxModalSytem = CKBMS
  ; coidentity      = record { N-ref = extK◻-ref }
  ; density         = record { denseN = dupK◻ ; denseN-ref = dupK◻-ref }
  }
  
-- imports ◻', etc.
open import USet.Box.CS4Box.Cover 𝕎₂ CS4BMS

-- imports ◻₊, etc. (modal localization holds for the imported definition!)
open FreeLocalizedCover WCS₊ renaming (LUSetCS4BoxA to ℛ)

------------------------
-- Model construction --
------------------------

◻-I' : {A : USet} → A ₀ (Δ , []) → ◻' A ₀ (Δ , Γ)
◻-I' x = (single _ _) , (λ { here → x })

Tm' : Form → USet
Tm' a = uset (uncurry (_⨾_⊢ a)) (uncurry wkTm)

∨-I1' : Tm' a →̇ Tm' (a ∨ b)
∨-I1' .apply = ∨-I1

∨-I2' : Tm' b →̇ Tm' (a ∨ b)
∨-I2' .apply = ∨-I2

Tm₊ : Form → LUSet
Tm₊ a = luset (Tm' a) (run𝒥' {Tm' a} localizeTm)
  where
  localizeTm : (k : K₊ Δ Γ) → ForAllW₊ k (uncurry (_⨾_⊢ a)) → Δ ⨾ Γ ⊢ a
  localizeTm (leaf _ _)       h = h here
  localizeTm (dead x)         h = ⊥-E x
  localizeTm (cons x k)       h = ◻-E x (localizeTm k (h ∘ there)) 
  localizeTm (branch x k1 k2) h = ∨-E x (localizeTm k1 (h ∘ left)) (localizeTm k2 (h ∘ right))

open import Instances.CS4Box.Semantics.Interpretation ℛ (Tm₊ ∘ 𝕡) hiding (◻'_)-- imports ⟦-⟧
open LUSet -- imports localize and 𝒳

◻-I₊ : {A : LUSet} → A .𝒳 ₀ (Δ , []) → (◻₊ A) .𝒳 ₀ (Δ , Γ)
◻-I₊ {A = luset A lA} x = (leaf _ _) , (λ { here → ◻-I' {A = A} x })

---------------------
-- Residualization --
---------------------

◻'-collect : ◻' (Tm' a) →̇ Tm' (◻ a)
◻'-collect {a} = ◻'-run {Tm' a} ◻'-collectAux
  where
  ◻'-collectAux : (k : K◻₂ Χ) (f : ForAllW◻ k (Tm' a ₀_)) → Tm' (◻ a) ₀ Χ
  ◻'-collectAux (single _ _)     f = ◻-I (f here)

◻₊-collect : ◻₊ (Tm₊ a) →̇₊ Tm₊ (◻ a)
◻₊-collect {a} = localize (Tm₊ (◻ a)) ∘' 𝒥'-map ◻'-collect 

◻₊-register : Tm₊ (◻ a) →̇₊ ◻₊ (Tm₊ a)
◻₊-register {a} .apply {Γ} n = cons n (leaf _ _) , λ { (there here) → single _ _ , λ { here → hypᵍ zero } }

reify   : ∀ a → ⟦ a ⟧ →̇₊ Tm₊ a
reflect : ∀ a → Tm₊ a →̇₊ ⟦ a ⟧

reify (𝕡 i)   = id'
reify ⊤       = fun (λ _ → ⊤-I)
reify ⊥       = Tm₊ ⊥ .localize ∘' 𝒥'-map (⊥'-elim {Tm' ⊥})
reify (a ⇒ b) = fun λ f → ⇒-I (reify b .apply (f (⊑-refl , freshWk) (reflect a .apply (hypˡ zero))))
reify (a ∧ b) = fun λ x → ∧-I (reify a .apply (proj₁ x)) (reify b .apply (proj₂ x))
reify (a ∨ b) = Tm₊ (a ∨ b) .localize ∘' 𝒥'-map [ ∨-I1' ∘' reify a  , ∨-I2' ∘' reify b ]'
reify (◻ a)   = ◻₊-collect ∘' ◻₊-map {⟦ a ⟧} {Tm₊ a} (reify a)

reflect (𝕡 i)   = id'
reflect ⊤       = unit'
reflect (a ⇒ b) = fun λ n i x → reflect b .apply (⇒-E (uncurry wkTm i n) (reify a .apply x))
reflect (a ∧ b) = fun λ n → reflect a .apply (∧-E1 n) , reflect b .apply (∧-E2 n)
reflect ⊥       = fun λ n → dead n , λ{()}
reflect (a ∨ b) = fun λ n → branch n (leaf _ (_ `, a)) (leaf _ (_ `, b)) ,
  λ { (left here)  → inj₁ (reflect a .apply (hypˡ zero))
    ; (right here) → inj₂ (reflect b .apply (hypˡ zero))
    }
reflect (◻ a)   = ◻₊-map {Tm₊ a} {⟦ a ⟧} (reflect a) ∘' ◻₊-register

------------------
-- Completeness --
------------------

import Instances.CS4Box.Semantics.Soundness as Soundness
open Soundness.Proof ℛ (Tm₊ ∘ 𝕡) using (⟦-⟧-sound)

idEnv : ∀ Χ → ⟦ Χ ⟧c₂ .𝒳 ₀ Χ
idEnv (Δ , Γ) = idEnvL Δ Γ , idEnvR Δ Γ
  where

  idEnvL : ∀ Δ Γ → (◻₊ ⟦ Δ ⟧c) .𝒳 ₀ (Δ , Γ)
  idEnvL []       Γ = ◻₊-distrib-⊤₊-back .apply _
  idEnvL (Δ `, a) Γ = ◻₊-distrib-×₊-back {X = ⟦ Δ ⟧c} {Y = ⟦ a ⟧} .apply
    ( wk₊ (◻₊ ⟦ Δ ⟧c) freshWkL₂ (idEnvL Δ Γ)
    , ◻-I₊ {A = ⟦ a ⟧} (reflect a .apply (hypᵍ zero)))

  idEnvR : ∀ Δ Γ → ⟦ Γ ⟧c .𝒳 ₀ (Δ , Γ)
  idEnvR Δ []       = _
  idEnvR Δ (Γ `, a) = wk₊ ⟦ Γ ⟧c freshWkR₂ (idEnvR Δ Γ) , reflect a .apply (hypˡ zero)

quot : (⟦ Δ , Γ ⟧c₂ →̇₊ ⟦ a ⟧) → Δ ⨾ Γ ⊢ a
quot {Δ} {Γ} {a} f = reify a .apply (f .apply (idEnv (Δ , Γ)))

completeness : Δ ⨾ Γ ⊨ₐ a → Δ ⨾ Γ ⊢ a
completeness f = quot (f ℛ (Tm₊ ∘ 𝕡))

