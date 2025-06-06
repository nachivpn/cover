{-# OPTIONS --safe #-}

module Instances.AbelS19 where

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)

open import PUtil

open import Function
open import Data.Sum

≡-cong₃ :
  {A A' A'' : Set} {B : Set}
  (f : A → A' → A'' → B)
  {x y : A} {x' y' : A'} {x'' y'' : A''}
  (p : x ≡ y) (q : x' ≡ y') (r : x'' ≡ y'')
  → ---------------------
  f x x' x'' ≡ f y y' y''
≡-cong₃ _ ≡-refl ≡-refl ≡-refl = ≡-refl

data Ty : Set where
  𝕓     : Ty
  𝟘     : Ty
  _+_   : Ty → Ty → Ty

private
  variable
    a b c d : Ty

open import Context Ty

data Ne : Ctx → Ty → Set where
  var : Var Γ a → Ne Γ a

data Nf : Ctx → Ty → Set where
  emb  : Ne Γ 𝕓 → Nf Γ 𝕓
  init : Ne Γ 𝟘 → Nf Γ a
  inl  : Nf Γ a → Nf Γ (a + b)
  inr  : Nf Γ b → Nf Γ (a + b)
  case : Ne Γ (a + b) → Nf (Γ `, a) c → Nf (Γ `, b) c → Nf Γ c

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNe i (var x) = var (wkVar i x)

wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a
wkNf i (emb x)       = emb (wkNe i x)
wkNf i (init x)      = init (wkNe i x)
wkNf i (inl n)       = inl (wkNf i n)
wkNf i (inr n)       = inr (wkNf i n)
wkNf i (case x n n') = case (wkNe i x) (wkNf (keep i) n) (wkNf (keep i) n')

wkNe-pres-refl : (n : Ne Γ a) → wkNe ⊆-refl n ≡ n
wkNe-pres-refl (var x) = ≡-cong var (wkVar-pres-⊆-refl x)

wkNe-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (n : Ne Γ a)
  → wkNe (⊆-trans i i') n ≡ wkNe i' (wkNe i n)
wkNe-pres-trans i i' (var x) = ≡-cong var (wkVar-pres-⊆-trans i i' x)

open import Frame.CFrame 𝒲

-- "Cover monad" in AbelS19
data 𝒞 (A : Ctx → Set) : Ctx → Set where
  return : A Γ → 𝒞 A Γ
  false  : Ne Γ 𝟘 → 𝒞 A Γ
  case   : Ne Γ (a + b) → 𝒞 A (Γ `, a) → 𝒞 A (Γ `, b) → 𝒞 A Γ

--
-- Reconstruction of the cover monad
--

data K : Ctx → Set where
  leaf    : (Γ : Ctx) → K Γ
  dead    : Ne Γ 𝟘 → K Γ
  branch  : Ne Γ (a + b) → K (Γ `, a) → K (Γ `, b) → K Γ

data _∈_ (Δ : Ctx) : K Γ → Set where
  here : Δ ∈ leaf Δ
  left : {n : Ne Γ (a + b)} {k : K (Γ `, a)} {k' : K (Γ `, b)}
    → Δ ∈ k → Δ ∈ branch n k k'
  right : {n : Ne Γ (a + b)} {k : K (Γ `, a)} {k' : K (Γ `, b)}
    → Δ ∈ k' → Δ ∈ branch n k k'

wkK : Γ ⊆ Γ' → K Γ → K Γ'
wkK i (leaf Δ)        = leaf _
wkK i (dead n)        = dead (wkNe i n)
wkK i (branch n k k') = branch (wkNe i n) (wkK (keep i) k) (wkK (keep i) k')

wkK-pres-refl : (k : K Γ) → wkK ⊆-refl k ≡ k
wkK-pres-refl (leaf _) = ≡-refl
wkK-pres-refl (dead n) = ≡-cong dead (wkNe-pres-refl n)
wkK-pres-refl (branch n k1 k2) = ≡-cong₃ branch (wkNe-pres-refl n) (wkK-pres-refl k1) (wkK-pres-refl k2)

wkK-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (k : K Γ)
  → wkK (⊆-trans i i') k ≡ wkK i' (wkK i k)
wkK-pres-trans i i' (leaf _) = ≡-refl
wkK-pres-trans i i' (dead x) = ≡-cong dead (wkNe-pres-trans i i' x)
wkK-pres-trans i i' (branch x k k₁) = ≡-cong₃
  branch (wkNe-pres-trans i i' x)
    (wkK-pres-trans (keep i) (keep i') k)
    (wkK-pres-trans (keep i) (keep i') k₁)

𝒦 : KPsh
𝒦 = record
  { K              = K
  ; wkK            = wkK
  ; wkK-pres-refl  = wkK-pres-refl
  ; wkK-pres-trans = wkK-pres-trans
  }

open {-CF.-}Core 𝒦 _∈_

factor : (i : Γ ⊆ Γ') (k : K Γ) → k ⊆k wkK i k
factor i (leaf _) here
  = _ , here , i
factor i (dead x) ()
factor i (branch x k1 k2) (left p)
  = let (Δ , p' , i') = factor (keep i) k1 p in
     (Δ , left p' , i')
factor i (branch x k1 k2) (right p)
  = let (Δ , p' , i') = factor (keep i) k2 p in
     (Δ , right p' , i')

factor-pres-refl : (k : K Γ) → factor ⊆-refl k ≋ ⊆k-refl[ k ]'
factor-pres-refl (leaf _) here = ≡-refl
factor-pres-refl (dead x) ()
factor-pres-refl (branch x k k') (left p)
  rewrite factor-pres-refl k p
    | wkNe-pres-refl x
    | wkK-pres-refl k
    | wkK-pres-refl k'         = ≡-refl
factor-pres-refl (branch x k k') (right p)
  rewrite factor-pres-refl k' p
    | wkNe-pres-refl x
    | wkK-pres-refl k
    | wkK-pres-refl k'         = ≡-refl

factor-pres-trans : (i : Γ ⊆ Γ') (i' : Γ' ⊆ Γ'') (k : K Γ) →
  factor (⊆-trans i i') k ≋ ⊆k-trans' k (factor i k) (factor i' (wkK i k))
factor-pres-trans i i' (leaf _) here       = ≡-refl
factor-pres-trans i i' (dead x) ()
factor-pres-trans i i' (branch x k k') (left p)
  rewrite factor-pres-trans (keep i) (keep i') k p
    | wkNe-pres-trans i i' x
    | wkK-pres-trans (keep i) (keep i') k
    | wkK-pres-trans (keep i) (keep i') k' = ≡-refl
factor-pres-trans i i' (branch x k k') (right p)
  rewrite factor-pres-trans (keep i) (keep i') k' p
    | wkNe-pres-trans i i' x
    | wkK-pres-trans (keep i) (keep i') k
    | wkK-pres-trans (keep i) (keep i') k' = ≡-refl

CF : CFrame
CF = record
  { factor            = factor
  ; factor-pres-refl  = factor-pres-refl
  ; factor-pres-trans = factor-pres-trans
  }

open Coverage

Cov : Coverage CF
Cov .family (leaf Γ)         here              = ⊆-refl
Cov .family (branch n k1 k2) (left x)  = freshWk ∙ Cov .family k1 x
Cov .family (branch n k1 k2) (right y) = freshWk ∙ Cov .family k2 y

Id : Identity CF
Id = record { idK[_] = leaf ; id∈ = λ { here → ≡-refl } }

-- imports USet, Cover' (the derived cover monad), etc.
open import USet.Base 𝒲 𝒦 (λ Δ k → Δ ∈ k) CF
open Pointed Id

module Equiv where

  𝒞' : USet → USet
  𝒞' A = uset (𝒞 (A ₀_)) wk𝒞
    where
    wk𝒞 : Γ ⊆ Γ' → 𝒞 (A ₀_) Γ → 𝒞 (A ₀_) Γ'
    wk𝒞 i (return x) = return (wk A i x)
    wk𝒞 i (false x) = false (wkNe i x)
    wk𝒞 i (case x m m') = case (wkNe i x) (wk𝒞 (keep i) m) (wk𝒞 (keep i) m')

  to : {A : USet} → 𝒞' A →̇ Cover' A
  to {A} .apply (return {Γ} x) = leaf Γ , λ { here → x }
  to {A} .apply (false x)      = dead x , λ { () }
  to {A} .apply (case x m m')  = let
    (k , f)   = to {A} .apply m
    (k' , f') = to {A} .apply m'
    in branch x k k' , λ
      { (left x) → f x
      ; (right y) → f' y
      }

  fromAux : {A : USet} {Γ : Ctx} → (k : K Γ) (f : ForAllW k (A ₀_)) → 𝒞 (A ₀_) Γ
  fromAux {A} (leaf Γ)        f = return (f {Γ} here)
  fromAux {A} (dead x)        f = false x
  fromAux {A} (branch x k k') f = case x (fromAux {A} k (f ∘ left)) (fromAux {A} k' (f ∘ right))

  from : {A : USet} → Cover' A →̇ 𝒞' A
  from {A} = runCover {A} (fromAux {A})

Nf' : Ty → USet
Nf' a = uset (λ Γ → Nf Γ a) wkNf

Ne' : Ty → USet
Ne' a = uset (λ Γ → Ne Γ a) wkNe

init' : Ne' 𝟘 →̇ Nf' 𝟘
init' .apply = init

emb' : Ne' 𝕓 →̇ Nf' 𝕓
emb' .apply = emb

inl' : Nf' a →̇ Nf' (a + b)
inl' .apply = inl

inr' : Nf' b →̇ Nf' (a + b)
inr' .apply = inr

⟦_⟧ : Ty → USet
⟦ 𝕓 ⟧     = Nf' 𝕓
⟦ 𝟘 ⟧     = Cover' (Ne' 𝟘)
⟦ a + b ⟧ = Cover' (⟦ a ⟧ ⊎' ⟦ b ⟧)

collectAux : (k : K Γ) (f : ForAllW k (Nf' a ₀_)) → Nf' a ₀ Γ
collectAux (leaf _) f         = f here
collectAux (dead n) f         = init n
collectAux (branch n k1 k2) f = case n (collectAux k1 (f ∘ left)) (collectAux k2 (f ∘ right))

collect : Cover' (Nf' a) →̇ Nf' a
collect {a} = runCover {Nf' a} collectAux

register+ : Ne' (a + b) →̇ Cover' (Ne' a ⊎' Ne' b)
register+ .apply n = (branch n (leaf _) (leaf _)) , λ
  { (left here)  → inj₁ (var zero)
  ; (right here) → inj₂ (var zero)
  }

reify : ∀ a → ⟦ a ⟧ →̇ Nf' a
reify 𝕓       = id'
reify 𝟘       = collect ∘' (mapCover' init')
reify (a + b) = collect ∘'  mapCover' [ inl' ∘' reify a  , inr' ∘' reify b ]'

reflect : ∀ a → Ne' a →̇ ⟦ a ⟧
reflect 𝕓       = emb'
reflect 𝟘       = return'
reflect (a + b) = mapCover' [ inj₁' ∘' reflect a ,  inj₂' ∘' reflect b ]' ∘' register+
