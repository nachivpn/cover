{-# OPTIONS --safe #-}

-- Dual Context K calculus
module Instances.Wish.DK where

open import Data.Product
  using (Σ; ∃; ∃₂; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

open import PUtil

open import Function

infix  3  _⨾_⊢_
infix  3  _⨾_⊢Ne_
infix  3  _⨾_⊢Nf_

data Ty : Set where
  𝕓  : Ty
  ◻_ : Ty → Ty

private
  variable
    a b c d : Ty

open import Context Ty

data _⨾_⊢_ (Δ Γ : Ctx) : Ty → Set where
  var   : (x : Var Γ a) → Δ ⨾ Γ ⊢ a
  box   : (t : [] ⨾ Δ ⊢ a) →  Δ ⨾ Γ ⊢ (◻ a)
  letin : (t : Δ ⨾ Γ ⊢ (◻ a)) → (u : (Δ `, a) ⨾ Γ ⊢ b) →  Δ ⨾ Γ ⊢ b

mutual
  data _⨾_⊢Ne_ (Δ Γ : Ctx) : Ty → Set where
    var : Var Γ a → Δ ⨾ Γ ⊢Ne a

  data _⨾_⊢Nf_ (Δ Γ : Ctx) : Ty → Set where
    up    : Δ ⨾ Γ ⊢Ne 𝕓 → Δ ⨾ Γ ⊢Nf 𝕓
    box   : [] ⨾ Δ ⊢Nf a → Δ ⨾ Γ ⊢Nf ◻ a
    letin : Δ ⨾ Γ ⊢Ne ◻ a → Δ `, a ⨾ Γ ⊢Nf ◻ b → Δ ⨾ Γ ⊢Nf ◻ b

wkNe : Δ ⊆ Δ' → Γ ⊆ Γ' → Δ ⨾ Γ ⊢Ne a → Δ' ⨾ Γ' ⊢Ne a
wkNe _ i (var x) = var (wkVar i x)

wkNf : Δ ⊆ Δ' → Γ ⊆ Γ' → Δ ⨾ Γ ⊢Nf a → Δ' ⨾ Γ' ⊢Nf a
wkNf i1 i2 (up x)      = up (wkNe i1 i2 x )
wkNf i1 i2 (box n)     = box (wkNf base i1 n)
wkNf i1 i2 (letin x n) = letin (wkNe i1 i2 x) (wkNf (keep i1) i2 n)

data Box (A : Ctx → Ctx → Set) (Δ Γ : Ctx) : Set where
  box    : A [] Δ → Box A Δ Γ
  letbox : Δ ⨾ Γ ⊢Ne (◻ a) → Box A (Δ `, a) Γ → Box A Δ Γ

data K : Ctx → Ctx → Set where
  single : (Δ : Ctx) (Γ : Ctx) → K Δ Γ
  cons   : Δ ⨾ Γ ⊢Ne (◻ a) → K (Δ `, a) Γ → K Δ Γ

data _⨾_∈_ : Ctx → Ctx → K Δ Γ → Set where
  here  : [] ⨾ Ξ ∈ single Ξ Θ
  there : {n : Δ ⨾ Γ ⊢Ne (◻ a)} {k : K (Δ `, a) Γ}
        → Ξ ⨾ Θ ∈ k → Ξ ⨾ Θ ∈ cons n k

there⁻¹ : {n : Δ ⨾ Γ ⊢Ne (◻ a)} {k : K (Δ `, a) Γ}
  → Ξ ⨾ Θ ∈ cons n k → Ξ ⨾ Θ ∈ k
there⁻¹ (there x) = x

Ctx₂ : Set
Ctx₂ = Ctx × Ctx

private
  variable
    Χ Χ' Χ'' Χ''' : Ctx₂

_⊆₂_ : Ctx × Ctx → Ctx × Ctx → Set
(Δ , Γ) ⊆₂ (Δ' , Γ') = Δ ⊆ Δ' × Γ ⊆ Γ'

⊆₂-trans : Χ ⊆₂ Χ' → Χ' ⊆₂ Χ'' → Χ ⊆₂ Χ''
⊆₂-trans (i1 , i2) (i1' , i2') = ⊆-trans i1 i1' , ⊆-trans i2 i2'

⊆₂-refl : Χ ⊆₂ Χ
⊆₂-refl = ⊆-refl , ⊆-refl

open import Frame.IFrame

𝕎₂ : Preorder Ctx₂ _⊆₂_
𝕎₂ = record
      { ⊆-trans            = ⊆₂-trans
      ; ⊆-refl             = ⊆₂-refl
      }

wkK : Δ ⊆ Δ' → Γ ⊆ Γ' → K Δ Γ → K Δ' Γ'
wkK i1 i2 (single _ _) = single _ _
wkK i1 i2 (cons x k)   = cons (wkNe i1 i2 x) (wkK (keep i1) i2 k)

K₂ = uncurry K

wkK₂ : Χ ⊆₂ Χ' → K₂ Χ → K₂ Χ'
wkK₂ = uncurry wkK

open import Frame.NFrame 𝕎₂

_∈_ : Ctx₂ → ∀ {Χ} → K₂ Χ → Set
Χ ∈ k = uncurry (_⨾_∈ k) Χ

open {-CF.-}Core K₂ _∈_

wkK-resp-⊆ : (i1 : Δ ⊆ Δ') (i2 : Γ ⊆ Γ') (k : K Δ Γ)
  → k ⊆k wkK i1 i2 k
wkK-resp-⊆ i1 i2 (single _ _) here      = _ , here , base , i1
wkK-resp-⊆ i1 i2 (cons x k)   (there p) =
  let (_ , p' , i1' , i2') = wkK-resp-⊆ (keep i1) i2 k p
  in _ , there p' , i1' , i2'

wkK₂-resp-⊆₂ : (i : Χ ⊆₂ Χ') (k : K₂ Χ) → k ⊆k wkK₂ i k
wkK₂-resp-⊆₂ = uncurry wkK-resp-⊆

NF : NFrame
NF = record { wkK = wkK₂ ; wkK-resp-⊆ = wkK₂-resp-⊆₂ }

_⊗_ : K₂ Χ → K₂ Χ → K₂ Χ
single _ _ ⊗ k' = k'
cons x k   ⊗ k' = cons x (k ⊗ wkK freshWk ⊆-refl k')

--TODO:
-- ⊗-bwd-reachable : (k1 k2 : K₂ Χ)
--   → ForAllW (k1 ⊗ k2)
--     (λ Χ' → ∃₂ (λ Χ1 Χ2 → (Χ1 ∈ k1 × Χ1 ⊆₂ Χ') × (Χ2 ∈ k2 × Χ2 ⊆₂ Χ')))
-- ⊗-bwd-reachable = {!!}

-- MNF : Magma NF
-- MNF = record { _⊗_ = _⊗_ ; ⊗-bwd-reachable = ⊗-bwd-reachable }

open import USet.Base 𝕎₂ K₂ _∈_ NF

module Equiv where

  𝒞' : USet → USet
  𝒞' A₂ = uset (uncurry (Box A)) (uncurry wkBox)
    where

    A : Ctx → Ctx → Set
    A = curry (A₂ ₀_)

    wkBox : Δ ⊆ Δ' → Γ ⊆ Γ' → Box A Δ Γ → Box A Δ' Γ'
    wkBox i1 i2 (box x)      = box (curry (wk A₂) base i1 x)
    wkBox i1 i2 (letbox x b) = letbox (wkNe i1 i2 x) (wkBox (keep i1) i2 b)

  to : {A : USet} → 𝒞' A →̇ Cover' A
  to {A} .apply (box x)      = single _ _ , λ { here → x }
  to {A} .apply (letbox x m) =
    let (k , f) = to {A} .apply m
      in cons x k , f ∘ there⁻¹

  fromAux : {A : USet} {Χ : Ctx₂} → (k : K₂ Χ) (f : ForAllW k (A ₀_)) → 𝒞' A ₀ Χ
  fromAux {A} (single _ _) f = box (f here)
  fromAux {A} (cons x k)   f = letbox x (fromAux {A} k (f ∘ there))

  from : {A : USet} → Cover' A →̇ 𝒞' A
  from {A} = runCover {A} (fromAux {A})
