{-# OPTIONS --safe #-}

module Instances.DualContextIK where

open import Data.Product
  using (Σ; ∃; ∃₂; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)

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

wkNe-pres-refl : (n : Δ ⨾ Γ ⊢Ne a) → wkNe ⊆-refl ⊆-refl n ≡ n
wkNe-pres-refl (var x) = ≡-cong var (wkVar-pres-⊆-refl x)

wkNe-pres-trans : (i1 : Δ ⊆ Δ') (i2 : Γ ⊆ Γ') (i1' : Δ' ⊆ Δ'') (i2' : Γ' ⊆ Γ'') (n : Δ ⨾ Γ ⊢Ne a)
  → wkNe (⊆-trans i1 i1') (⊆-trans i2 i2') n ≡ wkNe i1' i2' (wkNe i1 i2 n)
wkNe-pres-trans i1 i2 i1' i2' (var x) = ≡-cong var (wkVar-pres-⊆-trans i2 i2' x)

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

⊆₂-trans-assoc : (i : Χ ⊆₂ Χ') (i' : Χ' ⊆₂ Χ'') (i'' : Χ'' ⊆₂ Χ''')
  → ⊆₂-trans (⊆₂-trans i i') i'' ≡ ⊆₂-trans i (⊆₂-trans i' i'')
⊆₂-trans-assoc (i1 , i2) (i1' , i2') (i1'' , i2'')
  rewrite ⊆-trans-assoc i1 i1' i1''
  | ⊆-trans-assoc i2 i2' i2''
  = ≡-refl

⊆₂-refl : Χ ⊆₂ Χ
⊆₂-refl = ⊆-refl , ⊆-refl

⊆₂-trans-unit-left : (i : Χ ⊆₂ Χ') → ⊆₂-trans ⊆₂-refl i ≡ i
⊆₂-trans-unit-left (i1 , i2)
  rewrite ⊆-trans-unit-left i1
  | ⊆-trans-unit-left i2
  = ≡-refl

⊆₂-trans-unit-right : (i : Χ ⊆₂ Χ') → ⊆₂-trans i ⊆₂-refl ≡ i
⊆₂-trans-unit-right (i1 , i2)
  rewrite ⊆-trans-unit-right i1
  | ⊆-trans-unit-right i2
  = ≡-refl

open import Frame.IFrame

𝒲₂ : IFrame Ctx₂ _⊆₂_
𝒲₂ = record
      { ⊆-trans            = ⊆₂-trans
      ; ⊆-trans-assoc      = ⊆₂-trans-assoc
      ; ⊆-refl             = ⊆₂-refl
      ; ⊆-trans-unit-left  = ⊆₂-trans-unit-left
      ; ⊆-trans-unit-right = ⊆₂-trans-unit-right
      }

wkK : Δ ⊆ Δ' → Γ ⊆ Γ' → K Δ Γ → K Δ' Γ'
wkK i1 i2 (single _ _) = single _ _
wkK i1 i2 (cons x k)   = cons (wkNe i1 i2 x) (wkK (keep i1) i2 k)

wkK-pres-refl : (k : K Δ Γ) → wkK ⊆-refl ⊆-refl k ≡ k
wkK-pres-refl (single _ _)
  = ≡-refl
wkK-pres-refl (cons x k)
  = ≡-cong₂ cons (wkNe-pres-refl x) (wkK-pres-refl k)

wkK-pres-trans : (i1 : Δ ⊆ Δ') (i1' : Δ' ⊆ Δ'')
  → (i2 : Γ ⊆ Γ') (i2' : Γ' ⊆ Γ'') (k : K Δ Γ)
  → wkK (⊆-trans i1 i1') (⊆-trans i2 i2') k ≡ wkK i1' i2' (wkK i1 i2 k)
wkK-pres-trans i1 i1' i2 i2' (single _ _)
  = ≡-refl
wkK-pres-trans i1 i1' i2 i2' (cons x k)
  = ≡-cong₂ cons (wkNe-pres-trans i1 i2 i1' i2' x) (wkK-pres-trans (keep i1) (keep i1')  _ _ k)

K₂ = uncurry K

wkK₂ : Χ ⊆₂ Χ' → K₂ Χ → K₂ Χ'
wkK₂ = uncurry wkK

wkK₂-pres-refl : (k : K₂ Χ) → wkK₂ ⊆₂-refl k ≡ k
wkK₂-pres-refl k = wkK-pres-refl k

wkK₂-pres-trans : (i : Χ ⊆₂ Χ') (i' : Χ' ⊆₂ Χ'') (k : K₂ Χ)
  → wkK₂ (⊆₂-trans i i') k ≡ wkK₂ i' (wkK₂ i k)
wkK₂-pres-trans (i1 , i2) (i1' , i2') k = wkK-pres-trans i1 i1' i2 i2' k

open import Frame.CFrame 𝒲₂

𝒦 : KPsh
𝒦 = record
  { K              = K₂
  ; wkK            = wkK₂
  ; wkK-pres-refl  = wkK₂-pres-refl
  ; wkK-pres-trans = wkK₂-pres-trans
  }

_∈_ : Ctx₂ → ∀ {Χ} → K₂ Χ → Set
Χ ∈ k = uncurry (_⨾_∈ k) Χ

open {-CF.-}Core 𝒦 _∈_

factor : (i1 : Δ ⊆ Δ') (i2 : Γ ⊆ Γ') (k : K Δ Γ)
  → k ⊆k wkK i1 i2 k
factor i1 i2 (single _ _) here      = _ , here , base , i1
factor i1 i2 (cons x k)   (there p) =
  let (_ , p' , i1' , i2') = factor (keep i1) i2 k p
  in _ , there p' , i1' , i2'

factor-pres-refl : (k : K Δ Γ) → factor ⊆-refl ⊆-refl k ≋ ⊆k-refl[ k ]'
factor-pres-refl (single _ _) here
  = ≡-refl
factor-pres-refl (cons x k)   (there p)
  rewrite factor-pres-refl k p
  | wkNe-pres-refl x
  | wkK-pres-refl k
  = ≡-refl

factor-pres-trans : (i1 : Δ ⊆ Δ') (i2 : Γ ⊆ Γ') (i1' : Δ' ⊆ Δ'') (i2' : Γ' ⊆ Γ'') (k : K Δ Γ)
  → factor (⊆-trans i1 i1') (⊆-trans i2 i2') k
    ≋ ⊆k-trans' {i = i1 , i2} {i' = i1' , i2'} k (factor i1 i2 k) (factor i1' i2' (wkK i1 i2 k))
factor-pres-trans i1 i2 i1' i2' (single _ _) here
  = ≡-refl
factor-pres-trans i1 i2 i1' i2' (cons n k) (there p)
  rewrite factor-pres-trans (keep i1) i2 (keep i1') i2' k p
    | wkNe-pres-trans i1 i2 i1' i2' n
    | wkK-pres-trans (keep i1) (keep i1') i2 i2' k
  = ≡-refl

factor₂ : (i : Χ ⊆₂ Χ') (k : K₂ Χ) → k ⊆k wkK₂ i k
factor₂ = uncurry factor

factor₂-pres-refl : (k : K₂ Χ) → factor₂ ⊆₂-refl k ≋ ⊆k-refl[ k ]'
factor₂-pres-refl k = factor-pres-refl k

factor₂-pres-trans : (i : Χ ⊆₂ Χ') (i' : Χ' ⊆₂ Χ'') (k : K₂ Χ)
  → factor₂ (⊆₂-trans i i') k
    ≋ ⊆k-trans' {i = i} {i' = i'} k (factor₂ i k) (factor₂ i' (wkK₂ i k))
factor₂-pres-trans (i1 , i2) (i1' , i2') k = factor-pres-trans i1 i2 i1' i2' k

CF : CFrame
CF = record
  { factor            = factor₂
  ; factor-pres-refl  = factor₂-pres-refl
  ; factor-pres-trans = factor₂-pres-trans
  }

open import USet.Base 𝒲₂ 𝒦 _∈_ CF

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
