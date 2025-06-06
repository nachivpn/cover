{-# OPTIONS --safe #-}

module Instances.Maybe where

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
  emb  : Ne Γ 𝕓 → Nf Γ 𝕓
  just    : Nf Γ a → Nf Γ (𝕞 a)
  nothing : Nf Γ (𝕞 a)
  letin   : Ne Γ (𝕞 a) → Nf (Γ `, a) b → Nf Γ b

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNe i (var x) = var (wkVar i x)

wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a
wkNf i (emb x)     = emb (wkNe i x)
wkNf i (just n)    = just (wkNf i n)
wkNf i nothing     = nothing
wkNf i (letin n m) = letin (wkNe i n) (wkNf (keep i) m)

wkNe-pres-refl : (n : Ne Γ a) → wkNe ⊆-refl n ≡ n
wkNe-pres-refl (var x) = ≡-cong var (wkVar-pres-⊆-refl x)

wkNe-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (n : Ne Γ a)
  → wkNe (⊆-trans i i') n ≡ wkNe i' (wkNe i n)
wkNe-pres-trans i i' (var x) = ≡-cong var (wkVar-pres-⊆-trans i i' x)

open import Frame.CFrame 𝒲

-- the concrete residualising monad 𝒞
data 𝒞 (A : Ctx → Set) : Ctx → Set where
  return   : A Γ → 𝒞 A Γ
  nothing  : 𝒞 A Γ
  letin    : Ne Γ (𝕞 a) → 𝒞 A (Γ `, a) → 𝒞 A Γ

-- 𝒞 reconstructed using K and ∈
data K : Ctx → Set where
  single : (Γ : Ctx) → K Γ
  nil    : K Γ
  cons   : Ne Γ (𝕞 a) → K (Γ `, a) → K Γ

data _∈_ (Δ : Ctx) : K Γ → Set where
  here  : Δ ∈ single Δ
  there : {n : Ne Γ (𝕞 a)} {k : K (Γ `, a)} → Δ ∈ k → Δ ∈ cons n k

wkK : Γ ⊆ Γ' → K Γ → K Γ'
wkK i (single _) = single _
wkK i nil        = nil
wkK i (cons n k) = cons (wkNe i n) (wkK (keep i) k)

wkK-pres-refl : (k : K Γ) → wkK ⊆-refl k ≡ k
wkK-pres-refl (single _) = ≡-refl
wkK-pres-refl nil        = ≡-refl
wkK-pres-refl (cons n k) = ≡-cong₂ cons (wkNe-pres-refl n) (wkK-pres-refl k)

wkK-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (k : K Γ)
  → wkK (⊆-trans i i') k ≡ wkK i' (wkK i k)
wkK-pres-trans i i' (single _) = ≡-refl
wkK-pres-trans i i' nil        = ≡-refl
wkK-pres-trans i i' (cons n k) = ≡-cong₂
  cons (wkNe-pres-trans i i' n)
    (wkK-pres-trans (keep i) (keep i') k)

𝒦 : KPsh
𝒦 = record
  { K              = K
  ; wkK            = wkK
  ; wkK-pres-refl  = wkK-pres-refl
  ; wkK-pres-trans = wkK-pres-trans
  }

open {-CF.-}Core 𝒦 _∈_

factor : (i : Γ ⊆ Γ') (k : K Γ) → k ⊆k wkK i k
factor i (single _)   here
  = _ , here , i
factor i nil          ()
factor i (cons n k)   (there p)
  = let (Δ , p' , i') = factor (keep i) k p in
     (Δ , there p' , i')
factor-pres-refl : (k : K Γ) → factor ⊆-refl k ≋ ⊆k-refl[ k ]'
factor-pres-refl (single _)   here
  = ≡-refl
factor-pres-refl nil          ()
factor-pres-refl (cons n k) (there p)
  rewrite factor-pres-refl k p
    | wkNe-pres-refl n
    | wkK-pres-refl k
  = ≡-refl

factor-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (k : K Γ) →
  factor (⊆-trans i i') k ≋ ⊆k-trans' k (factor i k) (factor i' (wkK i k))
factor-pres-trans i i' (single _) here
  = ≡-refl
factor-pres-trans i i' nil        ()
factor-pres-trans i i' (cons n k) (there p)
  rewrite factor-pres-trans (keep i) (keep i') k p
    | wkNe-pres-trans i i' n
    | wkK-pres-trans (keep i) (keep i') k
  = ≡-refl

CF : CFrame
CF = record
  { factor            = factor
  ; factor-pres-refl  = factor-pres-refl
  ; factor-pres-trans = factor-pres-trans
  }

open Coverage

Cov : Coverage CF
Cov .family (single Γ) here      = ⊆-refl
Cov .family (cons n k) (there x) = freshWk ∙ Cov .family k x

Id : Identity CF
Id = record { idK[_] = single ; id∈ = λ { here → ≡-refl } }

-- imports USet, Cover' (the derived cover monad), etc.
open import USet.Base 𝒲 𝒦 (λ Δ k → Δ ∈ k) CF
open Pointed Id

Nf' : Ty → USet
Nf' a = uset (λ Γ → Nf Γ a) wkNf

Ne' : Ty → USet
Ne' a = uset (λ Γ → Ne Γ a) wkNe

emb' : Ne' 𝕓 →̇ Nf' 𝕓
emb' .apply = emb

just' : Nf' a →̇ Nf' (𝕞 a)
just' .apply = just

⟦_⟧ : Ty → USet
⟦ 𝕓   ⟧ = Nf' 𝕓
⟦ 𝕞 a ⟧ = Cover' (⟦ a ⟧)

collectAux : (k : K Γ) (f : ForAllW k (Nf' a ₀_)) → Nf' (𝕞 a) ₀ Γ
collectAux (single _)  f = just (f here)
collectAux nil         f = nothing
collectAux (cons n k)  f = letin n (collectAux k (f ∘ there))

collect : Cover' (Nf' a) →̇ Nf' (𝕞 a)
collect {a} = runCover {Nf' a} collectAux

register : Ne' (𝕞 a) →̇ Cover' (Ne' a)
register {a} .apply {Γ} n = (cons n (single (Γ `, a))) , λ { (there here) → var zero }

reify : ∀ a → ⟦ a ⟧ →̇ Nf' a
reify 𝕓     = id'
reify (𝕞 a) = collect ∘'  mapCover' (reify a)

reflect : ∀ a → Ne' a →̇ ⟦ a ⟧
reflect 𝕓     = emb'
reflect (𝕞 a) = mapCover' (reflect a) ∘' register
