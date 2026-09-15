{-# OPTIONS --safe --without-K #-}

module Instances.PLL.Semantics.Completeness where

open import HeytingAlgebras

open import Instances.PLL.System
open import Instances.PLL.Semantics.Entailment
import Instances.PLL.Semantics.Interpretation as Interpretation

open import Neighborhood.Systems 𝕎

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

open IPLBaseSystem ⊥ _∨_ _⊢_ wkTm

-------------------------
-- Lax modality system --
-------------------------

data K◇ : Ctx → Set where
  leaf    : (Γ : Ctx) → K◇ Γ
  dead    : Γ ⊢ ⊥ → K◇ Γ
  cons    : Γ ⊢ ◇ a → K◇ (Γ `, a) → K◇ Γ
  branch  : Γ ⊢ (a ∨ b) → K◇ (Γ `, a) → K◇ (Γ `, b) → K◇ Γ

data _∈◇_ (Δ : Ctx) : K◇ Γ → Set where
  here  : Δ ∈◇ leaf Δ
  there : {n : Γ ⊢ ◇ a} {k : K◇ (Γ `, a)} → Δ ∈◇ k → Δ ∈◇ cons n k
  left  : {n : Γ ⊢ (a ∨ b)} {k : K◇ (Γ `, a)} {k' : K◇ (Γ `, b)}
    → Δ ∈◇ k → Δ ∈◇ branch n k k'
  right : {n : Γ ⊢ (a ∨ b)} {k : K◇ (Γ `, a)} {k' : K◇ (Γ `, b)}
    → Δ ∈◇ k' → Δ ∈◇ branch n k k'

open import Neighborhood.Lib 𝕎 K◇ _∈◇_ using ()
    renaming (∣_∣ to ∣_∣◇ ; ForAllW to ForAllW◇) public

wkK◇ : Γ ⊑ Γ' → K◇ Γ → K◇ Γ'
wkK◇ i (leaf Δ)        = leaf _
wkK◇ i (dead n)        = dead (wkTm i n)
wkK◇ i (cons n k)      = cons (wkTm i n) (wkK◇ (keep i) k)
wkK◇ i (branch n k k') = branch (wkTm i n) (wkK◇ (keep i) k) (wkK◇ (keep i) k')

wkK◇-ref : (i : Γ ⊑ Γ') (k : K◇ Γ) → ∣ k ∣◇ ≼ ∣ wkK◇ i k ∣◇
wkK◇-ref i (leaf _) here
  = _ , here , i
wkK◇-ref i (dead x) ()
wkK◇-ref i (cons n k) (there p)
  = let (Δ , p' , i') = wkK◇-ref (keep i) k p in
     (Δ , there p' , i')
wkK◇-ref i (branch x k1 k2) (left p)
  = let (Δ , p' , i') = wkK◇-ref (keep i) k1 p in
     (Δ , left p' , i')
wkK◇-ref i (branch x k1 k2) (right p)
  = let (Δ , p' , i') = wkK◇-ref (keep i) k2 p in
     (Δ , right p' , i')

K◇-ref : (k : K◇ Γ) → ∣ k ∣◇ ⊆ (↑ Γ)
K◇-ref (leaf _)         here
  = ⊑-refl
K◇-ref (dead x)         ()
K◇-ref (cons n k)       (there p)
  = freshWk ∙ K◇-ref k p
K◇-ref (branch x k1 k2) (left p)
  = freshWk ∙ K◇-ref k1 p
K◇-ref (branch x k1 k2) (right p)
  = freshWk ∙ K◇-ref k2 p

idK◇ : (Γ : Ctx) → K◇ Γ
idK◇ = leaf

idK◇-sub : ∣ idK◇ Γ ∣◇ ⊆ ⟨ Γ ⟩
idK◇-sub here = ≡-refl
  
transK◇ : (k : K◇ Γ) → ForAllW◇ k K◇ → K◇ Γ
transK◇ (leaf _)        f = f here
transK◇ (dead x)        f = dead x
transK◇ (cons n k)      f = cons n (transK◇ k (f ∘ there))
transK◇ (branch x k k') f = branch x (transK◇ k (f ∘ left)) (transK◇ k' (f ∘ right))

transK◇-sub : (k : K◇ Γ) (h : ForAllW◇ k K◇)
  → ∣ (transK◇ k h) ∣◇ ⊆ ⨆ ∣ k ∣◇ (∣_∣◇ ∘ h)
transK◇-sub (leaf Γ)        h p
  = (Γ , here) , p
transK◇-sub (dead x)        h ()
transK◇-sub (cons n k)      h (there p) = 
  let (v' , p') , pl = transK◇-sub k (h ∘ there) p
  in (v' , there p') , pl
transK◇-sub (branch x k k') h (left p)  =
  let (vl , p') , pl = transK◇-sub k (h ∘ left) p
  in (vl , left p') , pl
transK◇-sub (branch x k k') h (right p) =
  let (vl , p') , pr = transK◇-sub k' (h ∘ right) p
  in (vl , right p') , pr

NS◇ : NeighborhoodSystem
NS◇ = record
  { N          = K◇
  ; _∈_        = _∈◇_
  ; refinement = record { wkN = wkK◇ ; wkN-ref = wkK◇-ref }
  }

CS◇ : CoverSystem NS◇
CS◇ = record
  { inclusion    = record { N-ref = K◇-ref }
  ; identity     = record { idN[_] = idK◇ ; idN-sub = idK◇-sub }
  ; transitivity = record { transN = transK◇ ; transN-sub = transK◇-sub }
  }

WCS◇ : WeakCoverSystem NS◇
WCS◇ = CoverSystem.weakCoverSystem CS◇

-- imports ◇', etc.
open import USet.Lax.PLL.Cover 𝕎 WCS◇

------------------------
-- Modal Localization --
------------------------

inclK◇ : K₊ Γ → K◇ Γ
inclK◇ (leaf _)        = leaf _
inclK◇ (dead x)        = dead x
inclK◇ (branch x k k') = branch x (inclK◇ k) (inclK◇ k')

inclK◇-sub : (k : K₊ Γ) → ∣ inclK◇ k ∣◇ ⊆ ∣ k ∣₊
inclK◇-sub (leaf _)        here      = here
inclK◇-sub (branch x k k') (left p)  = left (inclK◇-sub k p)
inclK◇-sub (branch x k k') (right p) = right (inclK◇-sub k' p)

incl' : {A : USet} → 𝒥' A →̇ ◇' A
incl' {A = A} .apply (k₊ , f) = inclK◇ k₊ , ⊆-trans {Y = ∣ k₊ ∣₊} (inclK◇-sub k₊) f

◇'-localize : {A : USet} → 𝒥' (◇' A) →̇ ◇' (𝒥' A)
◇'-localize {A} = (◇'-map (𝒥'-point {A}) ∘' ◇'-join {A}) ∘' incl' {◇' A} 

open LocalizedCover WCS₊ (λ {A} → ◇'-localize {A = A}) renaming (LUSetPLLA to ℛ)

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

◇'-collect : ◇' (Tm' a) →̇ Tm' (◇ a)
◇'-collect {a = a} = ◇'-run {Tm' a} collectAux
  where
  collectAux : (k : K◇ Γ) (f : ForAllW◇ k (Tm' a ₀_)) → Tm' (◇ a) ₀ Γ
  collectAux (leaf _)        f = ◇-I (f here)
  collectAux (dead x)        f = ⊥-E x
  collectAux (cons x k)      f = ◇-B x (collectAux k (f ∘ there))
  collectAux (branch x k k') f = ∨-E x (collectAux k (f ∘ left)) (collectAux k' (f ∘ right))

reify   : ∀ a → ⟦ a ⟧ →̇₊ (Tm₊ a)
reflect : ∀ a → Tm₊ a →̇₊ ⟦ a ⟧

reify (𝕡 i)   = id'
reify ⊤       = fun (λ _ → ⊤-I)
reify (a ⇒ b) = fun λ x → ⇒-I (reify b .apply (x freshWk (reflect a .apply (hyp zero))))
reify (a ∧ b) = fun λ x → ∧-I (reify a .apply (proj₁ x)) (reify b .apply (proj₂ x))
reify ⊥       = Tm₊ ⊥ .localize ∘' 𝒥'-map (⊥'-elim {Tm' ⊥})
reify (a ∨ b) = Tm₊ (a ∨ b) .localize ∘' 𝒥'-map [ ∨-I1' ∘' reify a  , ∨-I2' ∘' reify b ]'
reify (◇ a)   = ◇'-collect ∘' ◇'-map (reify a)

reflect (𝕡 i)   = id'
reflect ⊤       = unit'
reflect (a ⇒ b) = fun λ n i x → reflect b .apply (⇒-E (wkTm i n) (reify a .apply x))
reflect (a ∧ b) = fun λ n → reflect a .apply (∧-E1 n) , reflect b .apply (∧-E2 n)
reflect ⊥       = fun λ n → dead n , λ{()}
reflect (a ∨ b) = fun λ n → branch n (leaf (_ `, a)) (leaf (_ `, b)) ,
  λ { (left here)  → inj₁ (reflect a .apply (hyp zero))
    ; (right here) → inj₂ (reflect b .apply (hyp zero))
    }
reflect (◇ a)   = fun λ n → cons n (leaf (_ `, a)) ,
  λ { (there here) → reflect a .apply (hyp zero) }

------------------
-- Completeness --
------------------

idEnv : ∀ Γ → ⟦ Γ ⟧c .𝒳 ₀ Γ
idEnv []       = _
idEnv (Γ `, a) = wk (⟦ Γ ⟧c .𝒳) freshWk (idEnv Γ) , reflect a .apply (hyp zero)

quot : (⟦ Γ ⟧c →̇₊ ⟦ a ⟧) → Γ ⊢ a
quot {Γ} {a} f = reify a .apply (f .apply (idEnv Γ))

completeness : Γ ⊨ a → Γ ⊢ a
completeness f = quot (f ℛ (Tm₊ ∘ 𝕡))
