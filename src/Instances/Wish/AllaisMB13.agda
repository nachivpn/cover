{-# OPTIONS --safe #-}

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
  𝕃 : Ty → Ty

private
  variable
    a b c d : Ty

open import Context Ty

≡-cong₃ :
  {A A' A'' : Set} {B : Set}
  (f : A → A' → A'' → B)
  {x y : A} {x' y' : A'} {x'' y'' : A''}
  (p : x ≡ y) (q : x' ≡ y') (r : x'' ≡ y'')
  → ---------------------
  f x x' x'' ≡ f y y' y''
≡-cong₃ _ ≡-refl ≡-refl ≡-refl = ≡-refl

mutual
  data Ne : Ctx → Ty → Set where
    var  : Var Γ a → Ne Γ a
    fold : Nf ((Γ `, a) `, b) b → Nf Γ b → Ne Γ (𝕃 a) → Ne Γ b

  data Nf : Ctx → Ty → Set where
    emb   : Ne Γ 𝕓 → Nf Γ 𝕓
    nil   : Nf Γ (𝕃 b)
    cons  : Nf Γ b → Nf Γ (𝕃 b) → Nf Γ (𝕃 b)
    mapp  : Nf (Γ `, a) b → Ne Γ (𝕃 a) → Nf Γ (𝕃 b) → Nf Γ (𝕃 b)

mutual
  wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
  wkNe i (var x)      = var (wkVar i x)
  wkNe i (fold f b n) = fold (wkNf (keep (keep i)) f) (wkNf i b) (wkNe i n)

  wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a
  wkNf i (emb x)       = emb (wkNe i x)
  wkNf i nil           = nil
  wkNf i (cons n m)    = cons (wkNf i n) (wkNf i m)
  wkNf i (mapp m n m') = mapp (wkNf (keep i) m) (wkNe i n) (wkNf i m')

mutual
  wkNe-pres-refl : (n : Ne Γ a) → wkNe ⊆-refl n ≡ n
  wkNe-pres-refl (var x)      = ≡-cong var (wkVar-pres-⊆-refl x)
  wkNe-pres-refl (fold f b n) = ≡-cong₃ fold (wkNf-pres-refl f) (wkNf-pres-refl b) (wkNe-pres-refl n)

  wkNf-pres-refl : (n : Nf Γ a) → wkNf ⊆-refl n ≡ n
  wkNf-pres-refl (emb x)      = ≡-cong emb (wkNe-pres-refl x)
  wkNf-pres-refl nil          = ≡-refl
  wkNf-pres-refl (cons x xs)  = ≡-cong₂ cons (wkNf-pres-refl x) (wkNf-pres-refl xs)
  wkNf-pres-refl (mapp f x n) = ≡-cong₃ mapp (wkNf-pres-refl f) (wkNe-pres-refl x) (wkNf-pres-refl n)

mutual
  wkNe-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (n : Ne Γ a)
    → wkNe (⊆-trans i i') n ≡ wkNe i' (wkNe i n)
  wkNe-pres-trans i i' (var x)      = ≡-cong var (wkVar-pres-⊆-trans i i' x)
  wkNe-pres-trans i i' (fold f b n) = ≡-cong₃ fold
    (wkNf-pres-trans (keep (keep i)) (keep (keep i')) f)
    (wkNf-pres-trans i i' b)
    (wkNe-pres-trans i i' n)

  wkNf-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (n : Nf Γ a)
    → wkNf (⊆-trans i i') n ≡ wkNf i' (wkNf i n)
  wkNf-pres-trans i i' (emb x)       = ≡-cong emb (wkNe-pres-trans i i' x)
  wkNf-pres-trans i i' nil           = ≡-refl
  wkNf-pres-trans i i' (cons x xs)   = ≡-cong₂ cons (wkNf-pres-trans i i' x) (wkNf-pres-trans i i' xs)
  wkNf-pres-trans i i' (mapp f xs n) = ≡-cong₃ mapp
    (wkNf-pres-trans (keep i) (keep i') f)
    (wkNe-pres-trans i i' xs)
    (wkNf-pres-trans i i' n)

open import Frame.CFrame 𝒲

-- the actual residualising monad ℒ
data ℒ (A : Ctx → Set) : Ctx → Set where
  nil  : ℒ A Γ
  cons : A Γ → ℒ A Γ → ℒ A Γ
  mapp : (∀ {Γ'} → Γ ⊆ Γ' → Ne Γ' a → A Γ') → Ne Γ (𝕃 a) → ℒ A Γ → ℒ A Γ

-- a potential replacement for ℒ
data 𝒞 (A : Ctx → Set) : Ctx → Set where
  nil  : 𝒞 A Γ
  cons : A Γ → 𝒞 A Γ → 𝒞 A Γ
  mapp : (h : A (Γ `, a)) (n : Ne Γ (𝕃 a)) → 𝒞 A Γ → 𝒞 A Γ

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
  mapp : (n : Ne Γ (𝕃 a)) → K Γ → K Γ

data _∈_ : Ctx → {Γ : Ctx} → K Γ → Set where
  here-cons  : {k : K Γ} → Γ ∈ cons k
  there-cons : {k : K Γ} → Δ ∈ k → Δ ∈ cons k
  here-mapp  : {n : Ne Γ (𝕃 a)} {k : K Γ} → (Γ `, a) ∈ mapp n k
  there-mapp : {n : Ne Γ (𝕃 a)} {k : K Γ} → Δ ∈ k → Δ ∈ mapp n k

wkK : Γ ⊆ Γ' → K Γ → K Γ'
wkK i (nil _)    = nil _
wkK i (cons m)   = cons (wkK i m)
wkK i (mapp n m) = mapp (wkNe i n) (wkK i m)

wkK-pres-refl : (k : K Γ) → wkK ⊆-refl k ≡ k
wkK-pres-refl (nil _)    = ≡-refl
wkK-pres-refl (cons k)   = ≡-cong cons (wkK-pres-refl k)
wkK-pres-refl (mapp n k) = ≡-cong₂ mapp (wkNe-pres-refl n) (wkK-pres-refl k)

wkK-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (k : K Γ)
    → wkK (⊆-trans i i') k ≡ wkK i' (wkK i k)
wkK-pres-trans i i' (nil _)
  = ≡-refl
wkK-pres-trans i i' (cons k)
  = ≡-cong cons (wkK-pres-trans i i' k)
wkK-pres-trans i i' (mapp n k)
  = ≡-cong₂ mapp (wkNe-pres-trans i i' n) (wkK-pres-trans i i' k)

𝒦 : KPsh
𝒦 = record
  { K              = K
  ; wkK            = wkK
  ; wkK-pres-refl  = wkK-pres-refl
  ; wkK-pres-trans = wkK-pres-trans
  }

open {-CF.-}Core 𝒦 _∈_

factor : (i : Γ ⊆ Γ') (k : K Γ) → k ⊆k wkK i k
factor i (cons k)   here-cons      = _ , here-cons , i
factor i (cons k)   (there-cons p) =
  let (Δ , p' , i') = factor i k p
  in Δ , there-cons p' , i'
factor i (mapp n k) here-mapp      = _ , here-mapp , keep i
factor i (mapp n k) (there-mapp p)  =
  let (Δ , p' , i') = factor i k p
  in Δ , there-mapp p' , i'

factor-pres-refl : (k : K Γ)
    → factor ⊆-refl k ≋ ⊆k-refl[ k ]'
factor-pres-refl (cons k)   here-cons
  rewrite wkK-pres-refl k
  = ≡-refl
factor-pres-refl (cons k)   (there-cons p)
  rewrite factor-pres-refl k p
    | wkK-pres-refl k
  = ≡-refl
factor-pres-refl (mapp n k) here-mapp
  rewrite wkNe-pres-refl n
    | wkK-pres-refl k
  = ≡-refl
factor-pres-refl (mapp n k) (there-mapp p)
  rewrite wkNe-pres-refl n
    | factor-pres-refl k p
    | wkK-pres-refl k
  = ≡-refl

factor-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (k : K Γ)
    → factor (⊆-trans i i') k ≋ ⊆k-trans' k (factor i k) (factor i' (wkK i k))
factor-pres-trans i i' (cons k)   here-cons
  rewrite wkK-pres-trans i i' k
  = ≡-refl
factor-pres-trans i i' (cons k)   (there-cons p)
  rewrite factor-pres-trans i i' k p
    | wkK-pres-trans i i' k
  = ≡-refl
factor-pres-trans i i' (mapp n k) here-mapp
  rewrite wkNe-pres-trans i i' n
    | wkK-pres-trans i i' k
  = ≡-refl
factor-pres-trans i i' (mapp n k) (there-mapp p)
  rewrite factor-pres-trans i i' k p
    | wkNe-pres-trans i i' n
    | wkK-pres-trans i i' k
  = ≡-refl

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
  ⟦ 𝕃 a ⟧  = 𝒞' ⟦ a ⟧

  map𝒞 : {A B : USet} → (A →̇ B) → 𝒞' A →̇ 𝒞' B
  map𝒞 f .apply nil          = nil
  map𝒞 f .apply (cons x m)   = cons (f .apply x) (map𝒞 f .apply m)
  map𝒞 f .apply (mapp h n m) = mapp (f .apply h) n (map𝒞 f .apply m)

  collect : 𝒞' (Nf' a) →̇ Nf' (𝕃 a)
  collect .apply nil          = nil
  collect .apply (cons x m)   = cons x (collect .apply m)
  collect .apply (mapp h n m) = mapp h n (collect .apply m)

  register : Ne' (𝕃 a) →̇ 𝒞' (Ne' a)
  register .apply n = mapp (var zero) n nil

  reify : (a : Ty) → ⟦ a ⟧ →̇ Nf' a
  reify 𝕓     = emb'
  reify (𝕃 a) = collect ∘' map𝒞 (reify a)

  reflect : (a : Ty) → Ne' a →̇ ⟦ a ⟧
  reflect 𝕓     = id'
  reflect (𝕃 a) = map𝒞 (reflect a) ∘' register

  -- c.f. implementation of Mfold as in Figure 7
  fold𝒞 : (a b : Ty)
    → ({Γ' : Ctx} → Γ ⊆ Γ' → ⟦ a ⟧ ₀ Γ' → ⟦ b ⟧ ₀ Γ' → ⟦ b ⟧ ₀ Γ')
    → ⟦ b ⟧ ₀ Γ → 𝒞' ⟦ a ⟧ ₀ Γ → ⟦ b ⟧ ₀ Γ
  fold𝒞 a b C N nil            = N
  fold𝒞 a b C N (cons HD TL)   = C ⊆-refl HD (fold𝒞 a b C N TL)
  fold𝒞 a b C N (mapp F xs YS) = reflect b .apply (fold C' N' xs)
    where
    C' = reify b .apply (C (drop (drop ⊆-refl)) (wk ⟦ a ⟧ freshWk F) (reflect b .apply (var zero)))
    N' = reify b .apply (fold𝒞 a b C N YS)

  --
  -- Question: fold𝒞 is rather hacky, could a "foldMap" be a better behaved option?
  --
