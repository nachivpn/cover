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
  𝕓   : Ty
  _⇒_ : Ty → Ty → Ty
  𝕞   : Ty → Ty

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
  nothing : Tm Γ (𝕞 a)
  just    : Tm Γ a → Tm Γ (𝕞 a)
  letin   : Tm Γ (𝕞 a) → Tm (Γ `, a) (𝕞 b) → Tm Γ (𝕞 b)

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  var : Var Γ a → Ne Γ a
  app : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b

data Nf where
  emb     : Ne Γ 𝕓 → Nf Γ 𝕓
  lam     : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  just    : Nf Γ a → Nf Γ (𝕞 a)
  nothing : Nf Γ (𝕞 a)
  letin   : Ne Γ (𝕞 a) → Nf (Γ `, a) b → Nf Γ b

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a

wkNe i (var x)   = var (wkVar i x)
wkNe i (app n x) = app (wkNe i n) (wkNf i x)

wkNf i (emb x)     = emb (wkNe i x)
wkNf i (lam n)     = lam (wkNf (keep i) n)
wkNf i (just n)    = just (wkNf i n)
wkNf i nothing     = nothing
wkNf i (letin n m) = letin (wkNe i n) (wkNf (keep i) m)

--
-- Semantics
--

open import Frame.NFrame 𝕎

-- the concrete residualising monad (for illustration only)
data Maybe (A : Ctx → Set) : Ctx → Set where
  return   : A Γ → Maybe A Γ
  nothing  : Maybe A Γ
  letin    : Ne Γ (𝕞 a) → Maybe A (Γ `, a) → Maybe A Γ

-- Maybe reconstructed using K and ∈
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

open {-NF.-}Core K _∈_

wkK-resp-⊆ : (i : Γ ⊆ Γ') (k : K Γ) → k ⊆k wkK i k
wkK-resp-⊆ i (single _)   here
  = _ , here , i
wkK-resp-⊆ i nil          ()
wkK-resp-⊆ i (cons n k)   (there p)
  = let (Δ , p' , i') = wkK-resp-⊆ (keep i) k p in
     (Δ , there p' , i')

NF : NFrame
NF = record { wkK = wkK ; wkK-resp-⊆ = wkK-resp-⊆ }

open Reachable

RNF : Reachable NF
RNF .reachable (single Γ) here      = ⊆-refl
RNF .reachable (cons n k) (there x) = freshWk ∙ RNF .reachable k x

SPNF : StrictlyPointed NF
SPNF = record
  { pointK[_]         = single
  ; pointK-bwd-member = λ { here → ≡-refl }
  }

PNF = StrictlyPointed.pointed SPNF

joinK : (k : K Γ) → ForAllW k K → K Γ
joinK (single _) h = h here
joinK nil        h = nil
joinK (cons x k) h = cons x (joinK k (h ∘ there))

joinK-bwd-member : (k : K Γ) (h : ForAllW k K) → ForAllW (joinK k h) (λ Δ → Exists∈ k (λ Γ∈k → Δ ∈ h Γ∈k))
joinK-bwd-member (single _) h p
  = _ , here , p
joinK-bwd-member (cons x k) h (there p)
  = let (Δ , Γ∈k , Δ∈h-) = joinK-bwd-member k (h ∘ there) p
    in _ , there Γ∈k , Δ∈h-

SJNF : StrictlyJoinable NF
SJNF = record
  { joinK            = joinK
  ; joinK-bwd-member = joinK-bwd-member
  }

JNF = StrictlyJoinable.joinable SJNF

-- imports USet, Cover' (the derived cover monad), etc.
open import USet.Base 𝕎 K _∈_ NF renaming (Cover' to Maybe')

Nf' : Ty → USet
Nf' a = uset (λ Γ → Nf Γ a) wkNf

Ne' : Ty → USet
Ne' a = uset (λ Γ → Ne Γ a) wkNe

emb' : Ne' 𝕓 →̇ Nf' 𝕓
emb' .apply = emb

⟦_⟧ : Ty → USet
⟦ 𝕓     ⟧ = Nf' 𝕓
⟦ a ⇒ b ⟧ = ⟦ a ⟧ →' ⟦ b ⟧
⟦ 𝕞 a   ⟧ = Maybe' (⟦ a ⟧)

⟦_⟧c : Ctx → USet
⟦ [] ⟧c     = ⊤'
⟦ Γ `, a ⟧c = ⟦ Γ ⟧c ×' ⟦ a ⟧

--
-- Evaluation
--

nothing' : {G A : USet} → G →̇ Maybe' A
nothing' = fun (λ _ → nil , λ {()})

just' : {G A : USet} → G →̇ A → G →̇ Maybe' A
just' = Return.return' PNF

letin' : {G A B : USet} → (G →̇ Maybe' A) → ((G ×' A) →̇ Maybe' B) → (G →̇ Maybe' B)
letin' {G} {A} {B} = Letin.letin' RNF JNF {G} {A} {B}

evalVar : Var Γ a →  ⟦ Γ ⟧c →̇ ⟦ a ⟧
evalVar zero     = proj₂'
evalVar (succ x) = evalVar x ∘'  proj₁'

eval : Tm Γ a → ⟦ Γ ⟧c →̇ ⟦ a ⟧
eval (var x)             = evalVar x
eval (lam t)             = lam' (eval t)
eval (app t u)           = app' (eval t) (eval u)
eval (nothing {a = a})   = nothing' {A = ⟦ a ⟧}
eval (just t)            = just' (eval t)
eval (letin {b = b} t u) = letin' {B = ⟦ b ⟧} (eval t) (eval u)

--
-- Residualisation
--

collect : Maybe' (Nf' a) →̇ Nf' (𝕞 a)
collect {a} = runCover {Nf' a} collectAux
  where
  collectAux : (k : K Γ) (f : ForAllW k (Nf' a ₀_)) → Nf' (𝕞 a) ₀ Γ
  collectAux (single _)  f = just (f here)
  collectAux nil         f = nothing
  collectAux (cons n k)  f = letin n (collectAux k (f ∘ there))

register : Ne' (𝕞 a) →̇ Maybe' (Ne' a)
register {a} .apply {Γ} n = (cons n (single (Γ `, a))) , λ { (there here) → var zero }

reify : ∀ a → ⟦ a ⟧ →̇ Nf' a
reflect : ∀ a → Ne' a →̇ ⟦ a ⟧

reify 𝕓       = id'
reify (a ⇒ b) = fun λ f → lam (reify b .apply (f freshWk (reflect a .apply (var zero))))
reify (𝕞 a)   = collect ∘' mapCover' (reify a)

reflect 𝕓       = emb'
reflect (a ⇒ b) = fun λ n i x → reflect b .apply (app (wkNe i n) (reify a .apply x))
reflect (𝕞 a)   = mapCover' (reflect a) ∘' register

--
-- NbE
--

idEnv : ∀ Γ → ⟦ Γ ⟧c ₀ Γ
idEnv []       = _
idEnv (Γ `, a) = wk ⟦ Γ ⟧c freshWk (idEnv Γ) , reflect a .apply (var zero)

quot : (⟦ Γ ⟧c →̇ ⟦ a ⟧) → Nf Γ a
quot {Γ} {a} f = reify a .apply (f .apply (idEnv Γ))

norm : Tm Γ a → Nf Γ a
norm = quot ∘ eval
