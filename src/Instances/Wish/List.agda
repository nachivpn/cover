{-# OPTIONS --safe #-}

-- Extension of "New Equations for Neutral Terms"
-- (https://arxiv.org/abs/1304.0809)
module Instances.Wish.List where

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)

open import PUtil

open import Function
open import Data.Sum renaming ([_,_] to ⊎-match)

data Ty : Set where
  𝕓   : Ty
  _⇒_ : Ty → Ty → Ty
  𝕃   : Ty → Ty

private
  variable
    a b c d : Ty

open import Context Ty

--
-- Syntax
--

data Tm : Ctx → Ty → Set where
  var     : Var Γ a → Tm Γ a
  lam     : Tm (Γ `, a) b → Tm Γ (a ⇒ b)
  app     : Tm Γ (a ⇒ b) → Tm Γ a → Tm Γ b
  nothing : Tm Γ (𝕃 a)
  nil     : Tm Γ (𝕃 a)
  cons    : Tm Γ a → Tm Γ (𝕃 a) → Tm Γ (𝕃 a)
  append  : Tm Γ (𝕃 a) → Tm Γ (𝕃 a) → Tm Γ (𝕃 a)
  concat  : Tm Γ (𝕃 (𝕃 a)) → Tm Γ (𝕃 b)
  letmap  : Tm Γ (𝕃 a) → Tm (Γ `, a) b → Tm Γ (𝕃 b)

mutual
  data Ne : Ctx → Ty → Set where
    var  : Var Γ a → Ne Γ a
    fold : Nf ((Γ `, a) `, b) b → Nf Γ b → Ne Γ (𝕃 a) → Ne Γ b

  data Nf : Ctx → Ty → Set where
    emb    : Ne Γ 𝕓 → Nf Γ 𝕓
    nil    : Nf Γ (𝕃 b)
    cons   : Nf Γ b → Nf Γ (𝕃 b) → Nf Γ (𝕃 b)
    cmapp  : Nf (Γ `, a) (𝕃 b) → Ne Γ (𝕃 a) → Nf Γ (𝕃 b) → Nf Γ (𝕃 b)

mutual
  wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
  wkNe i (var x)      = var (wkVar i x)
  wkNe i (fold f b n) = fold (wkNf (keep (keep i)) f) (wkNf i b) (wkNe i n)

  wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a
  wkNf i (emb x)        = emb (wkNe i x)
  wkNf i nil            = nil
  wkNf i (cons n m)     = cons (wkNf i n) (wkNf i m)
  wkNf i (cmapp m n m') = cmapp (wkNf (keep i) m) (wkNe i n) (wkNf i m')

-- the concrete residualising monad (for illustration only)
data List (A : Ctx → Set) : Ctx → Set where
  nil   : List A Γ
  cons  : A Γ → List A Γ → List A Γ
  cmapp : (h : List A (Γ `, a)) (n : Ne Γ (𝕃 a)) → List A Γ → List A Γ

--
-- Deriving List using the cover modality
--

data K : Ctx → Set where
  nil   : (Γ : Ctx) → K Γ
  cons  : K Γ → K Γ
  cmapp : K (Γ `, a) → (n : Ne Γ (𝕃 a)) → K Γ → K Γ

data _∈_ : Ctx → {Γ : Ctx} → K Γ → Set where
  here-cons   : {k : K Γ} → Γ ∈ cons k
  there-cons  : {k : K Γ} → Δ ∈ k → Δ ∈ cons k
  left-cmapp  : {n : Ne Γ (𝕃 a)} {k1 : K (Γ `, a)} {k2 : K Γ} → Δ ∈ k1 → Δ ∈ cmapp k1 n k2
  right-cmapp : {n : Ne Γ (𝕃 a)} {k1 : K (Γ `, a)} {k2 : K Γ} → Δ ∈ k2 → Δ ∈ cmapp k1 n k2

open import Frame.NFrame 𝕎 K _∈_

wkK : Γ ⊆ Γ' → K Γ → K Γ'
wkK i (nil _)         = nil _
wkK i (cons m)        = cons (wkK i m)
wkK i (cmapp m1 n m2) = cmapp (wkK (keep i) m1) (wkNe i n) (wkK i m2)

wkK-refines : (i : Γ ⊆ Γ') (k : K Γ) → k ≼ wkK i k
wkK-refines i (cons k)   here-cons      = _ , here-cons , i
wkK-refines i (cons k)   (there-cons p) =
  let (Δ , p' , i') = wkK-refines i k p
  in Δ , there-cons p' , i'
wkK-refines i (cmapp k1 n k2) (left-cmapp p)  =
  let (Δ , p' , i') = wkK-refines (keep i) k1 p
  in Δ , left-cmapp p' , i'
wkK-refines i (cmapp k1 n k2) (right-cmapp p)  =
  let (Δ , p' , i') = wkK-refines i k2 p
  in Δ , right-cmapp p' , i'

MNF : Refinement
MNF = record { wkN = wkK ; wkN-refines = wkK-refines }

reachable : (k : K Γ) → ForAllW k (Γ ⊆_)
reachable (nil _)         ()
reachable (cons k)        here-cons
  = ⊆-refl
reachable (cons k)        (there-cons p)
  = reachable k p
reachable (cmapp k1 x k2) (left-cmapp p)
  = freshWk ∙ reachable k1 p
reachable (cmapp k1 x k2) (right-cmapp p)
  = reachable k2 p

-- Closure under union
_⊕_ : K Γ → K Γ → K Γ
(nil _)         ⊕ k' = k'
(cons k)        ⊕ k' = cons (k ⊕ k')
(cmapp k1 n k2) ⊕ k' = cmapp k1 n (k2 ⊕ k')

⊕-bwd-reachable : (k1 k2 : K Γ)
  → ForAllW (k1 ⊕ k2) λ v → v ∈ k1 ⊎ v ∈ k2
⊕-bwd-reachable (nil _)         k' p
  = inj₂ p
⊕-bwd-reachable (cons k)        k' here-cons
  = inj₁ here-cons
⊕-bwd-reachable (cons k)        k' (there-cons p)
  = ⊎-match (inj₁ ∘ there-cons) inj₂ (⊕-bwd-reachable k k' p)
⊕-bwd-reachable (cmapp k1 n k2) k' (left-cmapp p)
  = inj₁ (left-cmapp p)
⊕-bwd-reachable (cmapp k1 n k2) k' (right-cmapp p)
  = ⊎-match (inj₁ ∘ right-cmapp) inj₂ (⊕-bwd-reachable k2 k' p)

CNF : ClosedUnderUni
CNF = record { _⊕_ = _⊕_ ; ⊕-bwd-reachable = ⊕-bwd-reachable }

transK : (k : K Γ) → ForAllW k K → K Γ
transK (nil _)        f = nil _
transK (cons k)       f = (f here-cons) ⊕ (transK k (f ∘ there-cons))
transK (cmapp k x k') f = cmapp (transK k (f ∘ left-cmapp)) x (transK k' (f ∘ right-cmapp))

-- TODO: transK-bwd-reachable

ENF : Empty
ENF = record { emptyN[_] = nil ; emptyN-bwd-absurd = λ { () } }

open import USet.Base 𝕎
open import USet.Cover 𝕎 K _∈_ MNF renaming (𝒞' to List')

Nf' : Ty → USet
Nf' a = uset (λ Γ → Nf Γ a) wkNf

Ne' : Ty → USet
Ne' a = uset (λ Γ → Ne Γ a) wkNe

emb' : Ne' 𝕓 →̇ Nf' 𝕓
emb' .apply = emb

-- Bijection between concrete/direct and derived data types
module Bij where

  --
  CList' : USet → USet
  CList' A = uset (List (A ₀_)) wkList
    where
    wkList : Γ ⊆ Γ' → List (A ₀_) Γ → List (A ₀_) Γ'
    wkList i nil           = nil
    wkList i (cons x m)    = cons (wk A i x) (wkList i m)
    wkList i (cmapp h n m) = cmapp (wkList (keep i) h) (wkNe i n) (wkList i m)


  to : {A : USet} → CList' A →̇ List' A
  to {A} .apply nil          = nil _ , λ ()
  to {A} .apply (cons x m)   = let (k , f) = to {A} .apply m in
    (cons k) , λ
      { here-cons      → x
      ; (there-cons p) → f p
      }
  to {A} .apply (cmapp h n m) =
    let (k1 , f1) = to {A} .apply h
        (k2 , f2) = to {A} .apply m
    in (cmapp k1 n k2) , λ
       { (left-cmapp p) → f1 p
       ; (right-cmapp p) → f2 p
       }

  fromAux : {A : USet} {Γ : Ctx} → (k : K Γ) (f : ForAllW k (A ₀_)) → List (A ₀_) Γ
  fromAux {A} (nil _)         f = nil
  fromAux {A} (cons k)        f = cons (f here-cons) (fromAux {A} k (f ∘ there-cons))
  fromAux {A} (cmapp k1 n k2) f = cmapp (fromAux {A} k1 (f ∘ left-cmapp)) n (fromAux {A} k2 (f ∘ right-cmapp))

  from : {A : USet} → List' A →̇ CList' A
  from {A} = run𝒞' {A} (fromAux {A})

⟦_⟧ : Ty → USet
⟦ 𝕓     ⟧ = Nf' 𝕓
⟦ a ⇒ b ⟧ = ⟦ a ⟧ →' ⟦ b ⟧
⟦ 𝕃 a   ⟧ = List' (⟦ a ⟧)

⟦_⟧c : Ctx → USet
⟦ [] ⟧c     = ⊤'
⟦ Γ `, a ⟧c = ⟦ Γ ⟧c ×' ⟦ a ⟧
