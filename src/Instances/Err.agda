{-# OPTIONS --safe --without-K #-}

module Instances.Err where

open import Function using (_∘_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming ( refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
           ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst
           )

data Ty : Set where
  𝕓   : Ty
  _⇒_ : Ty → Ty → Ty
  𝕖   : Ty → Ty

private
  variable
    a b c d : Ty

open import Context Ty
open import Neighborhood.Systems 𝕎
open import USet.Base 𝕎

------------
-- Syntax --
------------

data Tm : Ctx → Ty → Set where
  var     : Var Γ a → Tm Γ a
  lam     : Tm (Γ `, a) b → Tm Γ (a ⇒ b)
  app     : Tm Γ (a ⇒ b) → Tm Γ a → Tm Γ b
  throw   : Tm Γ 𝕓 → Tm Γ (𝕖 a)
  return  : Tm Γ a → Tm Γ (𝕖 a)
  catch   : Tm Γ (𝕖 a) → Tm (Γ `, 𝕓) (𝕖 a) → Tm Γ (𝕖 a)
  letin   : Tm Γ (𝕖 a) → Tm (Γ `, a) (𝕖 b) → Tm Γ (𝕖 b)

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  var : Var Γ a → Ne Γ a
  app : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b

data Nf where
  emb     : Ne Γ 𝕓 → Nf Γ 𝕓
  lam     : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  throw   : Ne Γ 𝕓 → Nf Γ (𝕖 a)
  return  : Nf Γ a → Nf Γ (𝕖 a)
  tryunl  : Ne Γ (𝕖 a) → Nf (Γ `, a) (𝕖 b) → Nf (Γ `, 𝕓) (𝕖 b) → Nf Γ (𝕖 b)

wkNe : Γ ⊑ Γ' → Ne Γ a → Ne Γ' a
wkNf : Γ ⊑ Γ' → Nf Γ a → Nf Γ' a

wkNe i (var x)   = var (wkVar i x)
wkNe i (app n x) = app (wkNe i n) (wkNf i x)

wkNf i (emb x)          = emb (wkNe i x)
wkNf i (lam n)          = lam (wkNf (keep i) n)
wkNf i (return n)       = return (wkNf i n)
wkNf i (throw n)        = throw (wkNe i n)
wkNf i (tryunl n m1 m2) = tryunl (wkNe i n) (wkNf (keep i) m1) (wkNf (keep i) m2)

------------------
-- Cover system --
------------------

-- the concrete residualising monad (for reference only)
data Err (A : Ctx → Set) : Ctx → Set where
  return   : A Γ → Err A Γ
  throw    : Ne Γ 𝕓 → Err A Γ
  tryunl   : Ne Γ (𝕖 a) → Err A (Γ `, a) → Err A (Γ `, 𝕓) → Err A Γ

-- Err reconstructed using K and ∈
data K : Ctx → Set where
  single : (Γ : Ctx) → K Γ
  nil    : Ne Γ 𝕓 → K Γ
  branch : Ne Γ (𝕖 a) → K (Γ `, a) → K (Γ `, 𝕓) → K Γ

data _∈_ (Δ : Ctx) : K Γ → Set where
  here  : Δ ∈ single Δ
  left  : {n : Ne Γ (𝕖 a)} {k : K (Γ `, a)} {k' : K (Γ `, 𝕓)}
    → Δ ∈ k → Δ ∈ branch n k k'
  right : {n : Ne Γ (𝕖 a)} {k : K (Γ `, a)} {k' : K (Γ `, 𝕓)}
    → Δ ∈ k' → Δ ∈ branch n k k'

open import Neighborhood.Lib 𝕎 K _∈_

wkK : Γ ⊑ Γ' → K Γ → K Γ'
wkK i (single _)       = single _
wkK i (nil n)          = nil (wkNe i n)
wkK i (branch n k1 k2) = branch (wkNe i n) (wkK (keep i) k1) (wkK (keep i) k2)

wkK-ref : (i : Γ ⊑ Γ') (k : K Γ) → ∣ k ∣ ≼ ∣ wkK i k ∣
wkK-ref i (single _) here
  = _ , here , i
wkK-ref i (nil x) ()
wkK-ref i (branch x k1 k2) (left p)
  = let (Δ , p' , i') = wkK-ref (keep i) k1 p in
     (Δ , left p' , i')
wkK-ref i (branch x k1 k2) (right p)
  = let (Δ , p' , i') = wkK-ref (keep i) k2 p in
     (Δ , right p' , i')

K-ref : {Γ : Ctx} (k : K Γ) → ∣ k ∣ ⊆ (↑ Γ)
K-ref (single _)      here      = ⊑-refl
K-ref (branch x k k') (left p)  = ⊑-trans freshWk (K-ref k p)
K-ref (branch x k k') (right p) = ⊑-trans freshWk (K-ref k' p)

idK = single

idK-sub : {Γ : Ctx} → ∣ idK Γ ∣ ⊆ ⟨ Γ ⟩
idK-sub here = ≡-refl

transK : (k : K Γ) → ForAllW k K → K Γ
transK (single _)       h = h here
transK (nil n)          h = nil n
transK (branch n k1 k2) h = branch n (transK k1 (h ∘ left)) (transK k2 (h ∘ right))

transK-sub  : (k : K Γ) (h : ForAllW k K)
  → ∣ transK k h ∣ ⊆ ⨆ ∣ k ∣ (∣_∣ ∘ h)
transK-sub  (single Γ)      h p
  = (Γ , here) , p
transK-sub  (branch x k k') h (left p)  =
  let (vl , p') , pl = transK-sub  k (h ∘ left) p
  in (vl , left p') , pl
transK-sub  (branch x k k') h (right p) =
  let (vl , p') , pr = transK-sub  k' (h ∘ right) p
  in (vl , right p') , pr

NS : NeighborhoodSystem
NS = record
  { N          = K
  ; _∈_        = _∈_
  ; refinement = record { wkN = wkK ; wkN-ref = wkK-ref }
  }

-- imports USet, 𝒞' (the derived cover monad), etc.
open import USet.Cover 𝕎 NS renaming (𝒞' to Err')

CS : CoverSystem NS
CS = record
  { inclusion    = record { N-ref = K-ref }
  ; identity     = record { idN[_] = idK ; idN-sub = idK-sub }
  ; transitivity = record { transN = transK ; transN-sub = transK-sub }
  }

WCS = CoverSystem.weakCoverSystem CS

open StrongMonad WCS

--------------------
-- Interpretation --
--------------------

Nf' : Ty → USet
Nf' a = uset (λ Γ → Nf Γ a) wkNf

Ne' : Ty → USet
Ne' a = uset (λ Γ → Ne Γ a) wkNe

emb' : Ne' 𝕓 →̇ Nf' 𝕓
emb' .apply = emb

⟦_⟧ : Ty → USet
⟦ 𝕓     ⟧ = Ne' 𝕓
⟦ a ⇒ b ⟧ = ⟦ a ⟧ →' ⟦ b ⟧
⟦ 𝕖 a   ⟧ = Err' (⟦ a ⟧)

⟦_⟧c : Ctx → USet
⟦ [] ⟧c     = ⊤'
⟦ Γ `, a ⟧c = ⟦ Γ ⟧c ×' ⟦ a ⟧

----------------
-- Evaluation --
----------------

throw' : {G A : USet} → G →̇ Ne' 𝕓 → G →̇ Err' A
throw' t = fun λ g → nil (t .apply g) , λ { () }

catch' : {G A : USet} → (G →̇ Err' A) → ((G ×' Ne' 𝕓) →̇ Err' A) → (G →̇ Err' A)
catch' {A = A} t u .apply {Γ} g = let (k , f) = t .apply g in catchAux k f (curry' u .apply g)
  where
  catchAux : ∀ {Γ} (k : K Γ) (f : ForAllW k (A ₀_)) → (Ne' 𝕓 →' Err' A) ₀ Γ → Err' A ₀ Γ
  catchAux (single _)       f u = (single _) , f
  catchAux (nil n)          f u = u ⊑-refl n
  catchAux (branch x k1 k2) f u =
    let (k1' , f1') = catchAux k1 (f ∘ left) (u ∘ (freshWk ∙_))
        (k2' , f2') = catchAux k2 (f ∘ right) (u ∘ (freshWk ∙_))
    in (branch x k1' k2') , λ { (left p) → f1' p ; (right p) → f2' p }

evalVar : Var Γ a →  ⟦ Γ ⟧c →̇ ⟦ a ⟧
evalVar zero     = proj₂'
evalVar (succ x) = evalVar x ∘'  proj₁'

eval : Tm Γ a → ⟦ Γ ⟧c →̇ ⟦ a ⟧
eval (var x)             = evalVar x
eval (lam t)             = lam' (eval t)
eval (app t u)           = app' (eval t) (eval u)
eval (throw {a = a} t)   = throw' {A = ⟦ a ⟧} (eval t)
eval (catch {a = a} t u) = catch' {A = ⟦ a ⟧ } (eval t) (eval u)
eval (return t)          = return' (eval t)
eval (letin {b = b} t u) = letin' {B = ⟦ b ⟧} (eval t) (eval u)

---------------------
-- Residualisation --
---------------------

collect : Err' (Nf' a) →̇ Nf' (𝕖 a)
collect {a} =  run𝒞' {Nf' a} collectAux
  where
  collectAux : (k : K Γ) (f : ForAllW k (Nf' a ₀_)) → Nf' (𝕖 a) ₀ Γ
  collectAux (single _)       f = return (f here)
  collectAux (nil n)          f = throw n
  collectAux (branch n k1 k2) f = tryunl n (collectAux k1 (f ∘ left)) (collectAux k2 (f ∘ right))

register : Ne' (𝕖 a) →̇ Err' (Ne' a)
register {a} .apply {Γ} n = (branch n (single _) (nil (var zero))) , λ { (left here) → var zero }

reify : ∀ a → ⟦ a ⟧ →̇ Nf' a
reflect : ∀ a → Ne' a →̇ ⟦ a ⟧

reify 𝕓       = emb'
reify (a ⇒ b) = fun λ f → lam (reify b .apply (f freshWk (reflect a .apply (var zero))))
reify (𝕖 a)   = collect ∘' map𝒞' (reify a)

reflect 𝕓       = id'
reflect (a ⇒ b) = fun λ n i x → reflect b .apply (app (wkNe i n) (reify a .apply x))
reflect (𝕖 a)   = map𝒞' (reflect a) ∘' register

---------
-- NbE --
---------

idEnv : ∀ Γ → ⟦ Γ ⟧c ₀ Γ
idEnv []       = _
idEnv (Γ `, a) = wk ⟦ Γ ⟧c freshWk (idEnv Γ) , reflect a .apply (var zero)

quot : (⟦ Γ ⟧c →̇ ⟦ a ⟧) → Nf Γ a
quot {Γ} {a} f = reify a .apply (f .apply (idEnv Γ))

norm : Tm Γ a → Nf Γ a
norm = quot ∘ eval
