{-# OPTIONS --safe --without-K #-}

module Instances.CKBox.Semantics.NbE where

open import Instances.CKBox.System

open import Neighborhood.Systems 𝕎₂

open import Function using (_∘_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Product
  using (Σ; ∃; ∃₂; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl)

infix  3  _⨾_⊢Ne_
infix  3  _⨾_⊢Nf_

data _⨾_⊢Ne_ (Δ Γ : Ctx) : Form → Set
data _⨾_⊢Nf_ (Δ Γ : Ctx) : Form → Set

data _⨾_⊢Ne_ Δ Γ where
  hyp  : Var Γ a → Δ ⨾ Γ ⊢Ne a
  ⇒-E  : Δ ⨾  Γ ⊢Ne (a ⇒ b) → Δ ⨾ Γ ⊢Nf a → Δ ⨾ Γ ⊢Ne b
  ∧-E1 : Δ ⨾ Γ ⊢Ne (a ∧ b) → Δ ⨾ Γ ⊢Ne a
  ∧-E2 : Δ ⨾ Γ ⊢Ne (a ∧ b) → Δ ⨾ Γ ⊢Ne b

data _⨾_⊢Nf_ Δ Γ where
  emb  : Δ ⨾ Γ ⊢Ne (𝕡 i) → Δ ⨾ Γ ⊢Nf (𝕡 i)
  ⊥-E  : Δ ⨾ Γ ⊢Ne ⊥ → Δ ⨾ Γ ⊢Nf a
  ⊤-I  : Δ ⨾ Γ ⊢Nf ⊤
  ∧-I  : Δ ⨾ Γ ⊢Nf a → Δ ⨾ Γ ⊢Nf b → Δ ⨾ Γ ⊢Nf (a ∧ b)
  ⇒-I  : Δ ⨾ (Γ `, a) ⊢Nf b → Δ ⨾ Γ ⊢Nf (a ⇒ b)
  ◻-I  : [] ⨾ Δ ⊢Nf a → Δ ⨾ Γ ⊢Nf ◻ a
  ◻-E  : Δ ⨾ Γ ⊢Ne ◻ a → Δ `, a ⨾ Γ ⊢Nf ◻ b → Δ ⨾ Γ ⊢Nf ◻ b
  ∨-I1 : Δ ⨾ Γ ⊢Nf a → Δ ⨾ Γ ⊢Nf (a ∨ b)
  ∨-I2 : Δ ⨾ Γ ⊢Nf b → Δ ⨾ Γ ⊢Nf (a ∨ b)
  ∨-E  : Δ ⨾ Γ ⊢Ne (a ∨ b) → Δ ⨾ (Γ `, a) ⊢Nf c → Δ ⨾  (Γ `, b) ⊢Nf c → Δ ⨾ Γ ⊢Nf c

wkNe : Δ ⊑ Δ' → Γ ⊑ Γ' → Δ ⨾ Γ ⊢Ne a → Δ' ⨾ Γ' ⊢Ne a
wkNf : Δ ⊑ Δ' → Γ ⊑ Γ' → Δ ⨾ Γ ⊢Nf a → Δ' ⨾ Γ' ⊢Nf a

wkNe _  i  (hyp x)   = hyp (wkVar i x)
wkNe i1 i2 (⇒-E n m) = ⇒-E (wkNe i1 i2 n) (wkNf i1 i2 m)
wkNe i1 i2 (∧-E1 n)  = ∧-E1 (wkNe i1 i2 n)
wkNe i1 i2 (∧-E2 n)  = ∧-E2 (wkNe i1 i2 n)

wkNf i1 i2 (emb x)     = emb (wkNe i1 i2 x)
wkNf i1 i2 ⊤-I         = ⊤-I
wkNf i1 i2 (⊥-E x)     = ⊥-E (wkNe i1 i2 x)
wkNf i1 i2 (∧-I n m)   = ∧-I (wkNf i1 i2 n) (wkNf i1 i2 m)
wkNf i1 i2 (⇒-I x)     = ⇒-I (wkNf i1 (keep i2) x)
wkNf i1 i2 (◻-I n)     = ◻-I (wkNf base i1 n)
wkNf i1 i2 (◻-E x n)   = ◻-E (wkNe i1 i2 x) (wkNf (keep i1) i2 n)
wkNf i1 i2 (∨-I1 n)    = ∨-I1 (wkNf i1 i2 n)
wkNf i1 i2 (∨-I2 n)    = ∨-I2 (wkNf i1 i2 n)
wkNf i1 i2 (∨-E x n m) = ∨-E (wkNe i1 i2 x) (wkNf i1 (keep i2) n) (wkNf i1 (keep i2) m)

-----------------------
-- Base cover system --
-----------------------

data K₊ : Ctx → Ctx → Set where
  leaf    : (Δ Γ : Ctx) → K₊ Δ Γ
  dead    : Δ ⨾ Γ ⊢Ne ⊥ → K₊ Δ Γ
  branch  : Δ ⨾ Γ ⊢Ne (a ∨ b) → K₊ Δ (Γ `, a) → K₊ Δ (Γ `, b) → K₊ Δ Γ

data _⨾_∈₊_ : Ctx →  Ctx → K₊ Δ Γ → Set where
  here : Δ ⨾ Γ ∈₊ leaf Δ Γ
  left : {n : Δ ⨾ Γ ⊢Ne (a ∨ b)} {k : K₊ Δ (Γ `, a)} {k' : K₊ Δ (Γ `, b)}
    → Ξ ⨾ Θ ∈₊ k → Ξ ⨾ Θ ∈₊ branch n k k'
  right : {n : Δ ⨾ Γ ⊢Ne (a ∨ b)} {k : K₊ Δ (Γ `, a)} {k' : K₊ Δ (Γ `, b)}
    → Ξ ⨾ Θ ∈₊ k' → Ξ ⨾ Θ ∈₊ branch n k k'

K₊₂ = uncurry K₊

wkK₊ : Δ ⊑ Δ' → Γ ⊑ Γ' → K₊ Δ Γ → K₊ Δ' Γ'
wkK₊ i1 i2 (leaf _ _)       = leaf _ _
wkK₊ i1 i2 (dead x)         = dead (wkNe i1 i2 x)
wkK₊ i1 i2 (branch x k1 k2) = branch (wkNe i1 i2 x) (wkK₊ i1 (keep i2) k1) (wkK₊ i1 (keep i2) k2)

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
transK₊ (branch x k k') f = branch x (transK₊ k (f ∘ left)) (transK₊ k' (f ∘ right))

transK₊-sub : (k : K₊ Δ Γ) (h : ForAllW₊ k K₊₂)
  → ∣ transK₊ k h ∣₊ ⊆ ⨆ ∣ k ∣₊ (∣_∣₊ ∘ h)
transK₊-sub (leaf Δ Γ)      h p
  = ((Δ , Γ) , here) , p
transK₊-sub (dead x)        h ()
transK₊-sub (branch x k k') h (left p)  =
  let ((vl , p') , pl) = transK₊-sub k (h ∘ left) p
  in (vl , left p') , pl
transK₊-sub (branch x k k') h (right p) =
  let ((vl , p') , pr) = transK₊-sub k' (h ∘ right) p
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

---------------------
-- The ◻' modality --
---------------------

data K◻ : Ctx → Ctx → Set where
  single : (Δ : Ctx) (Γ : Ctx) → K◻ Δ Γ
  dead   : Δ ⨾ Γ ⊢Ne ⊥ → K◻ Δ Γ
  cons   : Δ ⨾ Γ ⊢Ne (◻ a) → K◻ (Δ `, a) Γ → K◻ Δ Γ
  branch : Δ ⨾ Γ ⊢Ne (a ∨ b) → K◻ Δ (Γ `, a) → K◻ Δ (Γ `, b) → K◻ Δ Γ

data _⨾_∈◻_ : Ctx → Ctx → K◻ Δ Γ → Set where
  here  : [] ⨾ Ξ ∈◻ single Ξ Θ
  there : {n : Δ ⨾ Γ ⊢Ne (◻ a)} {k : K◻ (Δ `, a) Γ}
        → Ξ ⨾ Θ ∈◻ k → Ξ ⨾ Θ ∈◻ cons n k
  left : {n : Δ ⨾ Γ ⊢Ne (a ∨ b)} {k : K◻ Δ (Γ `, a)} {k' : K◻ Δ (Γ `, b)}
    → Ξ ⨾ Θ ∈◻ k → Ξ ⨾ Θ ∈◻ branch n k k'
  right : {n : Δ ⨾ Γ ⊢Ne (a ∨ b)} {k : K◻ Δ (Γ `, a)} {k' : K◻ Δ (Γ `, b)}
    → Ξ ⨾ Θ ∈◻ k' → Ξ ⨾ Θ ∈◻ branch n k k'

there⁻¹ : {n : Δ ⨾ Γ ⊢Ne (◻ a)} {k : K◻ (Δ `, a) Γ}
  → Ξ ⨾ Θ ∈◻ cons n k → Ξ ⨾ Θ ∈◻ k
there⁻¹ (there x) = x

wkK◻ : Δ ⊑ Δ' → Γ ⊑ Γ' → K◻ Δ Γ → K◻ Δ' Γ'
wkK◻ i1 i2 (single _ _)     = single _ _
wkK◻ i1 i2 (cons x k)       = cons (wkNe i1 i2 x) (wkK◻ (keep i1) i2 k)
wkK◻ i1 i2 (dead x)         = dead (wkNe i1 i2 x)
wkK◻ i1 i2 (branch x k1 k2) = branch (wkNe i1 i2 x) (wkK◻ i1 (keep i2) k1) (wkK◻ i1 (keep i2) k2)

K◻₂ = uncurry K◻

wkK◻₂ : Χ ⊑₂ Χ' → K◻₂ Χ → K◻₂ Χ'
wkK◻₂ = uncurry wkK◻

_∈◻_ : Ctx₂ → ∀ {Χ} → K◻₂ Χ → Set
Χ ∈◻ k = uncurry (_⨾_∈◻ k) Χ

open import Neighborhood.Lib 𝕎₂ K◻₂ _∈◻_ using ()
  renaming (∣_∣ to ∣_∣◻ ; ForAllW to ForAllW◻)

wkK◻-ref : (i1 : Δ ⊑ Δ') (i2 : Γ ⊑ Γ') (k : K◻ Δ Γ)
  → ∣ k ∣◻ ≼ ∣ wkK◻ i1 i2 k ∣◻
wkK◻-ref i1 i2 (single _ _) here      = _ , here , base , i1
wkK◻-ref i1 i2 (cons x k)   (there p) =
  let (_ , p' , i1' , i2') = wkK◻-ref (keep i1) i2 k p
  in _ , there p' , i1' , i2'
wkK◻-ref i1 i2 (dead x) ()
wkK◻-ref i1 i2 (branch x k1 k2) (left p)
  = let (Δ , p' , i') = wkK◻-ref i1 (keep i2) k1 p in
     (Δ , left p' , i')
wkK◻-ref i1 i2 (branch x k1 k2) (right p)
  = let (Δ , p' , i') = wkK◻-ref i1 (keep i2) k2 p in
     (Δ , right p' , i')

wkK◻₂-ref₂ : (i : Χ ⊑₂ Χ') (k : K◻₂ Χ) → ∣ k ∣◻ ≼ ∣ wkK◻₂ i k ∣◻
wkK◻₂-ref₂ = uncurry wkK◻-ref

_⊗_ : K◻ Δ Γ → K◻ Δ Γ → K◻ Δ Γ
single Δ Γ     ⊗ k' = k'
cons x k       ⊗ k' = cons x (k ⊗ wkK◻₂ freshWkL₂ k')
dead x         ⊗ k' = dead x
branch x k1 k2 ⊗ k' = branch x (k1 ⊗ wkK◻₂ freshWkR₂ k') (k2 ⊗ wkK◻₂ freshWkR₂ k')

-- Note: Interestingly, this property doesn't hold due to branch
-- ∈-fwd-reachable : (k : K◻ Δ Γ) → Ξ ⨾ Θ ∈ k → Ξ ⊑ Γ

∈-bwd-reachable : (k : K◻ Δ Γ) → Ξ ⨾ Θ ∈◻ k → Δ ⊑ Θ
∈-bwd-reachable (single Δ Γ)     here      = ⊑-refl[ Δ ]
∈-bwd-reachable (cons x k)       (there p) = freshWk ∙ ∈-bwd-reachable k p
∈-bwd-reachable (dead x)         ()
∈-bwd-reachable (branch x k1 k2) (left p)  = ∈-bwd-reachable k1 p
∈-bwd-reachable (branch x k1 k2) (right p) = ∈-bwd-reachable k2 p

∈-bwd-reachable₂ : (k : K◻ Δ Γ) → Ξ ⨾ Θ ∈◻ k → ([] , Δ) ⊑₂ (Ξ , Θ)
∈-bwd-reachable₂ k p = ⊑-init[ _ ] , ∈-bwd-reachable k p

⊗-ref₁ : (k1 k2 : K◻ Δ Γ) → ∣ k1 ∣◻ ≼ ∣ k1 ⊗ k2 ∣◻
⊗-ref₁ (single Δ Γ) k2 {Ξ , Θ} p
  = ([] , Δ) , here , ∈-bwd-reachable₂ k2 p
⊗-ref₁ (cons x k1) k2 (there p)
  = let ((Δ , Γ) , p' , i') = ⊗-ref₁ k1 (wkK◻₂ freshWkL₂ k2) p
    in (Δ , Γ) , there p' , i'
⊗-ref₁ (branch x k1 _) k2 (left p)
  = let ((Δ , Γ) , p' , i') = ⊗-ref₁ k1 (wkK◻₂ freshWkR₂ k2) p
    in (Δ , Γ) , left p' , i'
⊗-ref₁ (branch x _ k1) k2 (right p)
  = let ((Δ , Γ) , p' , i') = ⊗-ref₁ k1 (wkK◻₂ freshWkR₂ k2) p
    in (Δ , Γ) , right p' , i'

⊗-ref₂ : (k1 k2 : K◻ Δ Γ) → ∣ k2 ∣◻ ≼ ∣ k1 ⊗ k2 ∣◻
⊗-ref₂ (single _ _)     k2 {Ξ , Θ} p
  = (Ξ , Θ) , p , ⊑₂-refl
⊗-ref₂ (cons x k1)      k2 (there p)
  = let ((Δ , Γ) , p' , i') = ⊗-ref₂ k1 (wkK◻₂ freshWkL₂ k2) p
        ((Δ' , Γ') , p'' , i'') = wkK◻-ref freshWk ⊑-refl k2 p'
    in (Δ' , Γ') , p'' , ⊑₂-trans i'' i'
⊗-ref₂ (branch x k1 _) k2 (left p)
  = let ((Δ , Γ) , p' , i') = ⊗-ref₂ k1 (wkK◻₂ freshWkR₂ k2) p
        ((Δ' , Γ') , p'' , i'') = wkK◻₂-ref₂ freshWkR₂ k2 p'
    in (Δ' , Γ') , p'' , ⊑₂-trans i'' i'
⊗-ref₂ (branch x _ k1) k2 (right p)
  = let ((Δ , Γ) , p' , i') = ⊗-ref₂ k1 (wkK◻₂ freshWkR₂ k2) p
        ((Δ' , Γ') , p'' , i'') = wkK◻₂-ref₂ freshWkR₂ k2 p'
    in (Δ' , Γ') , p'' , ⊑₂-trans i'' i'

unitK◻ : ∀ Χ → K◻₂ Χ
unitK◻ Χ = single _ _

NS◻ : NeighborhoodSystem
NS◻ = record
  { N          = K◻₂
  ; _∈_        = _∈◻_
  ; refinement = record { wkN = wkK◻₂ ; wkN-ref = wkK◻₂-ref₂ }
  }

CKMS◻ : CKBoxModalSystem NS◻
CKMS◻ = record
  { intclosed = record
    { _⊗_   = _⊗_
    ; ⊗-ref = λ k1 k2 → ⊗-ref₁ k1 k2 , ⊗-ref₂ k1 k2
    }
  ; seriality = record { unitN[_] = unitK◻ }
  }

-- imports ◻', etc.
open import USet.Box.CKBox.Cover 𝕎₂ CKMS◻

------------------------
-- Modal Localization --
------------------------

transK₊◻ : (k : K₊ Δ Γ) → ForAllW₊ k K◻₂ → K◻ Δ Γ
transK₊◻ (leaf _ _)       f = f here
transK₊◻ (dead x)         f = dead x
transK₊◻ (branch x k1 k2) f = branch x
  (transK₊◻ k1 (f ∘ left))
  (transK₊◻ k2 (f ∘ right))

transK₊◻-bwd-member : (k : K₊ Δ Γ) (h : ForAllW₊ k K◻₂)
  → ∣ transK₊◻ k h ∣◻ ⊆ ⨆ ∣ k ∣₊ (∣_∣◻ ∘ h)
transK₊◻-bwd-member (leaf Δ Γ)       f p         = ((Δ , Γ) , here) , p
transK₊◻-bwd-member (branch x k1 k2) f (left p)  =
  let ((Χ , p) , q) = transK₊◻-bwd-member k1 (f ∘ left) p
  in (Χ , left p) , q
transK₊◻-bwd-member (branch x k1 k2) f (right p) =
  let ((Χ , p) , q) = transK₊◻-bwd-member k2 (f ∘ right) p
  in (Χ , right p) , q

◻'-localize-imm : {A : USet} → 𝒥' (◻' A) →̇ ◻' A
◻'-localize-imm .apply (k , fam) = transK₊◻ k (proj₁ ∘ fam) , λ x →
  let (x , y) , z = transK₊◻-bwd-member k (proj₁ ∘ fam) x in (proj₂ ∘ fam) y z

◻'-localize : (A : USet) → 𝒥' (◻' A) →̇ ◻' (𝒥' A)
◻'-localize A = ◻'-map {A} {𝒥' A} 𝒥'-point ∘' ◻'-localize-imm {A}

open LocalizedCover WCS₊ (λ {A} → ◻'-localize A) renaming (LUSetCKBoxA to ℛ)

------------------------
-- Model construction --
------------------------

◻-I' : {A : USet} → A ₀ ([] , Δ) → ◻' A ₀ (Δ , Γ)
◻-I' x = (single _ _) , (λ { here → x })

Nf' : Form → USet
Nf' a = uset (uncurry (_⨾_⊢Nf a)) (uncurry wkNf)

Ne' : Form → USet
Ne' a = uset (uncurry (_⨾_⊢Ne a)) (uncurry wkNe)

emb' : Ne' (𝕡 i) →̇ Nf' (𝕡 i)
emb' .apply = emb

∨-I1' : Nf' a →̇ Nf' (a ∨ b)
∨-I1' .apply = ∨-I1

∨-I2' : Nf' b →̇ Nf' (a ∨ b)
∨-I2' .apply = ∨-I2

Nf₊ : Form → LUSet
Nf₊ a = luset (Nf' a) (run𝒥' {Nf' a} localizeNf)
  where
  localizeNf : (k : K₊ Δ Γ) → ForAllW₊ k (uncurry (_⨾_⊢Nf a)) → Δ ⨾ Γ ⊢Nf a
  localizeNf (leaf _ _)       h = h here
  localizeNf (dead x)         h = ⊥-E x
  localizeNf (branch x k1 k2) h = ∨-E x (localizeNf k1 (h ∘ left)) (localizeNf k2 (h ∘ right))

open import Instances.CKBox.Semantics.Interpretation ℛ (Nf₊ ∘ 𝕡) hiding (◻'_)-- imports ⟦-⟧
open LUSet -- imports localize and 𝒳

---------------------
-- Residualization --
---------------------

◻'-collect : ◻' (Nf' a) →̇ Nf' (◻ a)
◻'-collect {a} = ◻'-run {Nf' a} ◻'-collectAux
  where
  ◻'-collectAux : (k : K◻₂ Χ) (f : ForAllW◻ k (Nf' a ₀_)) → Nf' (◻ a) ₀ Χ
  ◻'-collectAux (single _ _)     f = ◻-I (f here)
  ◻'-collectAux (cons n k)       f = ◻-E n (◻'-collectAux k (f ∘ there))
  ◻'-collectAux (dead x)         f = ⊥-E x
  ◻'-collectAux (branch x k1 k2) f = ∨-E x (◻'-collectAux k1 (f ∘ left)) (◻'-collectAux k2 (f ∘ right))

◻'-register : Ne' (◻ a) →̇ ◻' (Ne' a)
◻'-register {a} .apply {Γ} n = cons n (single _ _) , λ { (there here) → hyp zero }

reify   : ∀ a → ⟦ a ⟧ →̇₊ Nf₊ a
reflect : ∀ a → Ne' a →̇ ⟦ a ⟧ .𝒳

reify (𝕡 i)   = id'
reify ⊤       = fun (λ _ → ⊤-I)
reify ⊥       = Nf₊ ⊥ .localize ∘' map𝒥' (⊥'-elim {Nf' ⊥})
reify (a ⇒ b) = fun λ f → ⇒-I (reify b .apply (f (⊑-refl , freshWk) (reflect a .apply (hyp zero))))
reify (a ∧ b) = fun λ x → ∧-I (reify a .apply (proj₁ x)) (reify b .apply (proj₂ x))
reify (a ∨ b) = Nf₊ (a ∨ b) .localize ∘' map𝒥' [ ∨-I1' ∘' reify a  , ∨-I2' ∘' reify b ]'
reify (◻ a)   = ◻'-collect ∘' ◻'-map (reify a)

reflect (𝕡 i)   = emb'
reflect ⊤       = unit'
reflect (a ⇒ b) = fun λ n i x → reflect b .apply (⇒-E (uncurry wkNe i n) (reify a .apply x))
reflect (a ∧ b) = fun λ n → reflect a .apply (∧-E1 n) , reflect b .apply (∧-E2 n)
reflect ⊥       = fun λ n → dead n , λ{()}
reflect (a ∨ b) = fun λ n → branch n (leaf _ (_ `, a)) (leaf _ (_ `, b)) ,
  λ { (left here)  → inj₁ (reflect a .apply (hyp zero))
    ; (right here) → inj₂ (reflect b .apply (hyp zero))
    }
reflect (◻ a)   = ◻'-map (reflect a) ∘' ◻'-register

---------
-- NbE --
---------

import Instances.CKBox.Semantics.Soundness as Soundness
open Soundness.Proof ℛ (Nf₊ ∘ 𝕡) using (⟦-⟧-sound)

idEnv : ∀ Χ → ⟦ Χ ⟧c₂ .𝒳 ₀ Χ
idEnv (Δ , Γ) = idEnvL Δ Γ , idEnvR Δ Γ
  where
  
  idEnvL : ∀ Δ Γ → (◻₊ ⟦ Δ ⟧c) .𝒳 ₀ (Δ , Γ)
  idEnvL []       Γ = single [] Γ , λ x → _
  idEnvL (Δ `, a) Γ = ◻'-pair {A = ⟦ Δ ⟧c .𝒳} {B = ⟦ a ⟧ .𝒳} proj₁' proj₂' .apply
    (wk₊ (◻₊ ⟦ Δ ⟧c) freshWkL₂ (idEnvL Δ Γ)
    , ◻-I' {A = ⟦ a ⟧ .𝒳} (reflect a .apply (hyp zero)))

  idEnvR : ∀ Δ Γ → ⟦ Γ ⟧c .𝒳 ₀ (Δ , Γ)
  idEnvR Δ []       = _
  idEnvR Δ (Γ `, a) = wk₊ ⟦ Γ ⟧c freshWkR₂ (idEnvR Δ Γ) , reflect a .apply (hyp zero)

quot : (⟦ Δ , Γ ⟧c₂ →̇₊ ⟦ a ⟧) → Δ ⨾ Γ ⊢Nf a
quot {Δ} {Γ} {a} f = reify a .apply (f .apply (idEnv (Δ , Γ)))

nbe : Δ ⨾ Γ ⊢ a → Δ ⨾ Γ ⊢Nf a
nbe t = quot (⟦-⟧-sound t)
