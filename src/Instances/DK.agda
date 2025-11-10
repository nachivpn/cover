{-# OPTIONS --safe #-}

-- Dual Context K calculus
module Instances.DK where

open import Data.Product
  using (Σ; ∃; ∃₂; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

open import PUtil

open import Function

infix  3  _⨾_⊢_
infix  3  _⨾_⊢Ne_
infix  3  _⨾_⊢Nf_

data Ty : Set where
  𝕓  : Ty
  _⇒_ : Ty → Ty → Ty
  ◻_ : Ty → Ty

private
  variable
    a b c d : Ty

open import Context Ty

data _⨾_⊢_ (Δ Γ : Ctx) : Ty → Set where
  var   : (x : Var Γ a) → Δ ⨾ Γ ⊢ a
  lam   : Δ ⨾ (Γ `, a) ⊢ b → Δ ⨾ Γ ⊢ (a ⇒ b)
  app   : Δ ⨾ Γ ⊢ (a ⇒ b) → Δ ⨾ Γ ⊢ a → Δ ⨾ Γ ⊢ b
  box   : (t : [] ⨾ Δ ⊢ a) →  Δ ⨾ Γ ⊢ (◻ a)
  letin : (t : Δ ⨾ Γ ⊢ (◻ a)) → (u : (Δ `, a) ⨾ Γ ⊢ b) →  Δ ⨾ Γ ⊢ b

mutual
  data _⨾_⊢Ne_ (Δ Γ : Ctx) : Ty → Set where
    var : Var Γ a → Δ ⨾ Γ ⊢Ne a
    app : Δ ⨾  Γ ⊢Ne (a ⇒ b) → Δ ⨾ Γ ⊢Nf a → Δ ⨾ Γ ⊢Ne b

  data _⨾_⊢Nf_ (Δ Γ : Ctx) : Ty → Set where
    emb   : Δ ⨾ Γ ⊢Ne 𝕓 → Δ ⨾ Γ ⊢Nf 𝕓
    lam   : Δ ⨾ (Γ `, a) ⊢Nf b → Δ ⨾ Γ ⊢Nf (a ⇒ b)
    box   : [] ⨾ Δ ⊢Nf a → Δ ⨾ Γ ⊢Nf ◻ a
    letin : Δ ⨾ Γ ⊢Ne ◻ a → Δ `, a ⨾ Γ ⊢Nf ◻ b → Δ ⨾ Γ ⊢Nf ◻ b

wkNe : Δ ⊆ Δ' → Γ ⊆ Γ' → Δ ⨾ Γ ⊢Ne a → Δ' ⨾ Γ' ⊢Ne a
wkNf : Δ ⊆ Δ' → Γ ⊆ Γ' → Δ ⨾ Γ ⊢Nf a → Δ' ⨾ Γ' ⊢Nf a

wkNe _  i  (var x)   = var (wkVar i x)
wkNe i1 i2 (app n m) = app (wkNe i1 i2 n) (wkNf i1 i2 m)

wkNf i1 i2 (emb x)     = emb (wkNe i1 i2 x )
wkNf i1 i2 (lam x)     = lam (wkNf i1 (keep i2) x)
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

_∈_ : Ctx₂ → ∀ {Χ} → K₂ Χ → Set
Χ ∈ k = uncurry (_⨾_∈ k) Χ

open import Frame.NFrame 𝕎₂ K₂ _∈_

wkK-refines : (i1 : Δ ⊆ Δ') (i2 : Γ ⊆ Γ') (k : K Δ Γ)
  → k ≼ wkK i1 i2 k
wkK-refines i1 i2 (single _ _) here      = _ , here , base , i1
wkK-refines i1 i2 (cons x k)   (there p) =
  let (_ , p' , i1' , i2') = wkK-refines (keep i1) i2 k p
  in _ , there p' , i1' , i2'

wkK₂-refines₂ : (i : Χ ⊆₂ Χ') (k : K₂ Χ) → k ≼ wkK₂ i k
wkK₂-refines₂ = uncurry wkK-refines

NF : Refinement
NF = record { wkN = wkK₂ ; wkN-refines = wkK₂-refines₂ }

_⊗_ : K Δ Γ → K Δ Γ → K Δ Γ
single Δ Γ ⊗ k' = k'
cons x k   ⊗ k' = cons x (k ⊗ wkK freshWk ⊆-refl k')

∈-fwd-reachable : (k : K Δ Γ) → Ξ ⨾ Θ ∈ k → Ξ ⊆ Γ
∈-fwd-reachable (single Δ Γ) here      = ⊆-init[ Γ ]
∈-fwd-reachable (cons x k)   (there p) = ∈-fwd-reachable k p

∈-bwd-reachable : (k : K Δ Γ) → Ξ ⨾ Θ ∈ k → Δ ⊆ Θ
∈-bwd-reachable (single Δ Γ) here = ⊆-refl[ Δ ]
∈-bwd-reachable (cons x k)   (there p) = freshWk ∙ ∈-bwd-reachable k p

∈-bwd-reachable₂ : (k : K Δ Γ) → Ξ ⨾ Θ ∈ k → ([] , Δ) ⊆₂ (Ξ , Θ)
∈-bwd-reachable₂ k p = ⊆-init[ _ ] , ∈-bwd-reachable k p

⊗-bwd-reachable : (k1 k2 : K Δ Γ) → ForAllW (k1 ⊗ k2)
     (λ Χ' → ∃₂ (λ Χ1 Χ2 → Χ1 ∈ k1 × Χ1 ⊆₂ Χ' × Χ2 ∈ k2 × Χ2 ⊆₂ Χ'))
⊗-bwd-reachable (single Δ Γ) k      {Ξ , Θ}       p
  = ([] , Δ) , (Ξ , Θ)
  , here , ∈-bwd-reachable₂ k p
  , p    , ⊆₂-refl
⊗-bwd-reachable (cons x k1) k2       {Ξ , Θ}     (there p)
  = let ((Δ1 , Γ1) , (Δ2 , Γ2) , p1 , i1 , p2 , i2) = ⊗-bwd-reachable k1 (wkK freshWk ⊆-refl k2) p
        ((Δ2' , Γ2') , p2' , i2') = wkK-refines freshWk ⊆-refl k2 p2
    in _ , _
      , there p1 , i1
      , p2' , ⊆₂-trans i2' i2

WCNF : WeaklyClosedUnderInt
WCNF = record { _⊗_ = _⊗_ ; ⊗-bwd-reachable = ⊗-bwd-reachable }

unitK : ∀ Χ → K₂ Χ
unitK Χ = single _ _

UNF : NonEmpty
UNF = record { unitN[_] = unitK }

open import USet.Base 𝕎₂
open import USet.Cover 𝕎₂ K₂ _∈_ NF renaming (𝒞' to Box')

box' : {A : USet} → A ₀ ([] , Δ) → Box' A ₀ (Δ , Γ)
box' x = (single _ _) , (λ { here → x })

Nf' : Ty → USet
Nf' a = uset (uncurry (_⨾_⊢Nf a)) (uncurry wkNf)

Ne' : Ty → USet
Ne' a = uset (uncurry (_⨾_⊢Ne a)) (uncurry wkNe)

emb' : Ne' 𝕓 →̇ Nf' 𝕓
emb' .apply = emb

⟦_⟧ : Ty → USet
⟦ 𝕓     ⟧ = Nf' 𝕓
⟦ a ⇒ b ⟧ = ⟦ a ⟧ →' ⟦ b ⟧
⟦ ◻ a   ⟧ = Box' (⟦ a ⟧)

⟦_⟧c : Ctx → USet
⟦ [] ⟧c     = ⊤'
⟦ Γ `, a ⟧c = ⟦ Γ ⟧c ×' ⟦ a ⟧

⟦_⟧c₂ : Ctx₂ → USet
⟦ Δ , Γ ⟧c₂ = Box' ⟦ Δ ⟧c ×' ⟦ Γ ⟧c

evalVar : Var Γ a →  ⟦ Γ ⟧c →̇ ⟦ a ⟧
evalVar zero     = proj₂'
evalVar (succ x) = evalVar x ∘'  proj₁'

letin' : {D G A B : USet}
  → (Box' D ×' G) →̇ Box' A
  → (Box' (D ×' A) ×' G) →̇ B
  → (Box' D ×' G) →̇ B
letin' {D} {G} {A} = ×'-distr.letin' WCNF {D = D} {A = A}

prBox' : {G A B : USet} → G →̇ Box' A → G →̇ Box' B → G →̇ Box' (A ×' B)
prBox' {G} {A} {B} = ×'-distr.pr𝒞' WCNF {G = G} {A = A} {B = B}

unitBox' : {G : USet} → G →̇ Box' ⊤'
unitBox' = ⊤'-distr.unit𝒞' UNF

eval : Δ ⨾ Γ ⊢ a → ⟦ Δ , Γ ⟧c₂ →̇ ⟦ a ⟧
eval (var x)
  = evalVar x ∘' proj₂'
eval (lam {a = a} {b} t)
  = lam' {A = ⟦ a ⟧} {B = ⟦ b ⟧} (eval t ∘' x'-right-assoc)
eval (app t u)
  = app' (eval t) (eval u)
eval {Δ} {Γ} (box {a = a} t)
  = map𝒞' {A = ⟦ Δ ⟧c} {B = ⟦ a ⟧} (eval t ∘' ⟨ unitBox' {G = ⟦ Δ ⟧c } , id' ⟩') ∘' proj₁'
eval {Δ} (letin {a = a} t u)
  = letin' {D = ⟦ Δ ⟧c} {A = ⟦ a ⟧} (eval t) (eval u)

--
-- Residualisation
--

collect : Box' (Nf' a) →̇ Nf' (◻ a)
collect {a} = run𝒞' {Nf' a} collectAux
  where
  collectAux : (k : K₂ Χ) (f : ForAllW k (Nf' a ₀_)) → Nf' (◻ a) ₀ Χ
  collectAux (single _ _) f = box (f here)
  collectAux (cons n k)   f = letin n (collectAux k (f ∘ there))

register : Ne' (◻ a) →̇ Box' (Ne' a)
register {a} .apply {Γ} n = cons n (single _ _) , λ { (there here) → var zero }

reify   : ∀ a → ⟦ a ⟧ →̇ Nf' a
reflect : ∀ a → Ne' a →̇ ⟦ a ⟧

reify 𝕓       = id'
reify (a ⇒ b) = fun λ f → lam (reify b .apply (f (⊆-refl , freshWk) (reflect a .apply (var zero))))
reify (◻ a)   = collect ∘' map𝒞' (reify a)

reflect 𝕓       = emb'
reflect (a ⇒ b) = fun λ n i x → reflect b .apply (app (uncurry wkNe i n) (reify a .apply x))
reflect (◻ a)   = map𝒞' (reflect a) ∘' register

--
-- NbE
--

idEnv : ∀ Χ → ⟦ Χ ⟧c₂ ₀ Χ
idEnv (Δ , Γ) = idEnv1 Δ Γ , idEnv2 Δ Γ
  where
  idEnv1 : ∀ Δ Γ → Box' ⟦ Δ ⟧c ₀ (Δ , Γ)
  idEnv1 []       Γ = single [] Γ , λ x → _
  idEnv1 (Δ `, a) Γ = prBox' {G = Box' ⟦ Δ ⟧c ×' Box' ⟦ a ⟧} {A = ⟦ Δ ⟧c} {B = ⟦ a ⟧} proj₁' proj₂' .apply
    (wk (Box' ⟦ Δ ⟧c) (freshWk , ⊆-refl) (idEnv1 Δ Γ)
    , box' {A = ⟦ a ⟧} (reflect a .apply (var zero)))

  idEnv2 : ∀ Δ Γ → ⟦ Γ ⟧c ₀ (Δ , Γ)
  idEnv2 Δ []       = _
  idEnv2 Δ (Γ `, a) = wk ⟦ Γ ⟧c (⊆-refl , freshWk) (idEnv2 Δ Γ) , reflect a .apply (var zero)

quot : (⟦ Δ , Γ ⟧c₂ →̇ ⟦ a ⟧) → Δ ⨾ Γ ⊢Nf a
quot {Δ} {Γ} {a} f = reify a .apply (f .apply (idEnv (Δ , Γ)))

norm : Δ ⨾ Γ ⊢ a → Δ ⨾ Γ ⊢Nf a
norm = quot ∘ eval

module Equiv where

  𝒞' : USet → USet
  𝒞' A₂ = uset (uncurry (Box A)) (uncurry wkBox)
    where

    A : Ctx → Ctx → Set
    A = curry (A₂ ₀_)

    wkBox : Δ ⊆ Δ' → Γ ⊆ Γ' → Box A Δ Γ → Box A Δ' Γ'
    wkBox i1 i2 (box x)      = box (curry (wk A₂) base i1 x)
    wkBox i1 i2 (letbox x b) = letbox (wkNe i1 i2 x) (wkBox (keep i1) i2 b)

  to : {A : USet} → 𝒞' A →̇ Box' A
  to {A} .apply (box x)      = single _ _ , λ { here → x }
  to {A} .apply (letbox x m) =
    let (k , f) = to {A} .apply m
      in cons x k , f ∘ there⁻¹

  fromAux : {A : USet} {Χ : Ctx₂} → (k : K₂ Χ) (f : ForAllW k (A ₀_)) → 𝒞' A ₀ Χ
  fromAux {A} (single _ _) f = box (f here)
  fromAux {A} (cons x k)   f = letbox x (fromAux {A} k (f ∘ there))

  from : {A : USet} → Box' A →̇ 𝒞' A
  from {A} = run𝒞' {A} (fromAux {A})
