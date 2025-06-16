--{-# OPTIONS --safe #-}

-- "New Equations for Neutral Terms"
-- (https://arxiv.org/abs/1304.0809)
module Instances.Wish.AllaisMB13 where

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)

open import PUtil

open import Function
open import Data.Sum

data Ty : Set where
  𝕓 : Ty
  𝕞 : Ty → Ty

private
  variable
    a b c d : Ty

open import Context Ty

data Ne : Ctx → Ty → Set where
  var : Var Γ a → Ne Γ a

data Nf : Ctx → Ty → Set where
  emb   : Ne Γ 𝕓 → Nf Γ 𝕓
  nil   : Nf Γ (𝕞 b)
  cons  : Nf Γ b → Nf Γ (𝕞 b) → Nf Γ (𝕞 b)
  mapp  : Nf (Γ `, a) b → Ne Γ (𝕞 a) → Nf Γ (𝕞 b) → Nf Γ (𝕞 b)

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNe i (var x) = var (wkVar i x)

wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a
wkNf i (emb x)        = emb (wkNe i x)
wkNf i nil            = nil
wkNf i (cons n m)     = cons (wkNf i n) (wkNf i m)
wkNf i (mapp m n m') = mapp (wkNf (keep i) m) (wkNe i n) (wkNf i m')

wkNe-pres-refl : (n : Ne Γ a) → wkNe ⊆-refl n ≡ n
wkNe-pres-refl (var x) = ≡-cong var (wkVar-pres-⊆-refl x)

wkNe-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (n : Ne Γ a)
  → wkNe (⊆-trans i i') n ≡ wkNe i' (wkNe i n)
wkNe-pres-trans i i' (var x) = ≡-cong var (wkVar-pres-⊆-trans i i' x)

open import Frame.CFrame 𝒲

-- the actual residualising monad ℒ
data ℒ (A : Ctx → Set) : Ctx → Set where
  nil  : ℒ A Γ
  cons : A Γ → ℒ A Γ → ℒ A Γ
  mapp : (∀ {Γ'} → Γ ⊆ Γ' → Ne Γ' a → A Γ') → Ne Γ (𝕞 a) → ℒ A Γ → ℒ A Γ

-- a potential replacement for ℒ
data 𝒞 (A : Ctx → Set) : Ctx → Set where
  nil  : 𝒞 A Γ
  cons : A Γ → 𝒞 A Γ → 𝒞 A Γ
  mapp : (h : A (Γ `, a)) (n : Ne Γ (𝕞 a)) → 𝒞 A Γ → 𝒞 A Γ

-- (special case of) "internal" map𝒞
imap𝒞 : {A B : Ctx → Set}
  → (∀ {Γ'} → Γ ⊆ Γ' → A Γ' → B Γ')
  → 𝒞 A Γ → 𝒞 B Γ
imap𝒞 f nil          = nil
imap𝒞 f (cons x m)   = cons (f ⊆-refl x) (imap𝒞 f m)
imap𝒞 f (mapp h n m) = mapp (f freshWk h) n (imap𝒞 f m)

_++_ : {A : Ctx → Set} → 𝒞 A Γ → 𝒞 A Γ → 𝒞 A Γ
nil         ++ m2 = m2
cons x m1   ++ m2 = cons x (m1 ++ m2)
mapp h n m1 ++ m2 = mapp h n (m1 ++ m2)

-- Deriving ℒ

data K : Ctx → Set where
  nil  : (Γ : Ctx) → K Γ
  cons : K Γ → K Γ
  mapp : (n : Ne Γ (𝕞 a)) → K Γ → K Γ

data _∈_ : Ctx → {Γ : Ctx} → K Γ → Set where
  here-nil   : Γ ∈ nil Γ
  here-cons  : {k : K Γ} → Γ ∈ cons k
  there-cons : {k : K Γ} → Δ ∈ k → Δ ∈ cons k
  here-mapp  : {n : Ne Γ (𝕞 a)} {k : K Γ} → (Γ `, a) ∈ mapp n k
  there-mapp : {n : Ne Γ (𝕞 a)} {k : K Γ} → Δ ∈ k → Δ ∈ mapp n k

wkK : Γ ⊆ Γ' → K Γ → K Γ'
wkK i (nil _)    = nil _
wkK i (cons m)   = cons (wkK i m)
wkK i (mapp n m) = mapp (wkNe i n) (wkK i m)

-- doable, TBD
postulate
  wkK-pres-refl : (k : K Γ) → wkK ⊆-refl k ≡ k
  wkK-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (k : K Γ)
    → wkK (⊆-trans i i') k ≡ wkK i' (wkK i k)

𝒦 : KPsh
𝒦 = record
  { K              = K
  ; wkK            = wkK
  ; wkK-pres-refl  = wkK-pres-refl
  ; wkK-pres-trans = wkK-pres-trans
  }

open {-CF.-}Core 𝒦 _∈_

factor : (i : Γ ⊆ Γ') (k : K Γ) → k ⊆k wkK i k
factor i (nil _)    here-nil       = _ , here-nil , i
factor i (cons k)   here-cons      = _ , here-cons , i
factor i (cons k)   (there-cons p) =
  let (Δ , p' , i') = factor i k p
  in Δ , there-cons p' , i'
factor i (mapp n k) here-mapp      = _ , here-mapp , keep i
factor i (mapp n k) (there-mapp p)  =
  let (Δ , p' , i') = factor i k p
  in Δ , there-mapp p' , i'

postulate

  factor-pres-refl : (k : K Γ)
    → factor ⊆-refl k ≋ ⊆k-refl[ k ]'

  factor-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (k : K Γ)
    → factor (⊆-trans i i') k ≋ ⊆k-trans' k (factor i k) (factor i' (wkK i k))

CF : CFrame
CF = record
  { factor            = factor
  ; factor-pres-refl  = factor-pres-refl
  ; factor-pres-trans = factor-pres-trans
  }

open import USet.Base 𝒲 𝒦 _∈_ CF -- USet, Cover'. etc.

Nf' : Ty → USet
Nf' a = uset (λ Γ → Nf Γ a) wkNf

Ne' : Ty → USet
Ne' a = uset (λ Γ → Ne Γ a) wkNe

emb' : Ne' 𝕓 →̇ Nf' 𝕓
emb' .apply = emb

𝒞' : USet → USet
𝒞' A = uset (𝒞 (A ₀_)) wk𝒞
  where
  wk𝒞 : Γ ⊆ Γ' → 𝒞 (A ₀_) Γ → 𝒞 (A ₀_) Γ'
  wk𝒞 i nil          = nil
  wk𝒞 i (cons x m)   = cons (wk A i x) (wk𝒞 i m)
  wk𝒞 i (mapp h n m) = mapp (wk A (keep i) h) (wkNe i n) (wk𝒞 i m)

-- A direct implementation (without Cover')
module Direct where

  ⟦_⟧ : Ty → USet
  ⟦ 𝕓 ⟧    = Ne' 𝕓
  ⟦ 𝕞 a ⟧  = 𝒞' ⟦ a ⟧

  map𝒞 : {A B : USet} → (A →̇ B) → 𝒞' A →̇ 𝒞' B
  map𝒞 f .apply nil          = nil
  map𝒞 f .apply (cons x m)   = cons (f .apply x) (map𝒞 f .apply m)
  map𝒞 f .apply (mapp h n m) = mapp (f .apply h) n (map𝒞 f .apply m)

  collect : 𝒞' (Nf' a) →̇ Nf' (𝕞 a)
  collect .apply nil          = nil
  collect .apply (cons x m)   = cons x (collect .apply m)
  collect .apply (mapp h n m) = mapp h n (collect .apply m)

  register : Ne' (𝕞 a) →̇ 𝒞' (Ne' a)
  register .apply n = mapp (var zero) n nil

  reify : (a : Ty) → ⟦ a ⟧ →̇ Nf' a
  reify 𝕓     = emb'
  reify (𝕞 a) = collect ∘' map𝒞 (reify a)

  reflect : (a : Ty) → Ne' a →̇ ⟦ a ⟧
  reflect 𝕓     = id'
  reflect (𝕞 a) = map𝒞 (reflect a) ∘' register
