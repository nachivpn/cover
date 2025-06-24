*Meeting with Andreas Abel and Nachi about the "Cover modality"*

We covered:

1. Scope and expressivity of the cover modality
2. Compositionaliy in constructing residualising functors
3. Relationship to indexed containers

### Applications

There appear to be two main applications for the cover modality:

- Generalising intuitionistic necessity and possibility modalities
  with "confluence"/"factorisation" conditions
- Constructing residualising functors used in NbE models
  systematically

### Scope for NbE

Using the cover modality, we wish to reconstruct existing residualising functors found in:

- Flinski (2001). Normalization by Evaluation for the Computational Lambda-Calculus.
- Lindley (2009). Accumulating bindings.
- Ahman and Staton (2013). Normalization by Evaluation and Algebraic Effects.
- Allais, McBride and Boutillier (2013). New equations for neutral terms: a sound and complete decision procedure, formalized.
- Abel and Sattler (2019). Normalization by Evaluation for Call-by-Push-Value and Polarized Lambda-Calculus.
- Valliappan, Russo and Lindley (2021). Practical Normalization by Evaluation for EDSLs.
- Daggitt, Atkey and Kokke (2023). Compiling Higher-Order Specifications to SMT Solvers: How to Deal with Rejection Constructively.
- Atkey and Kokke (2024). A Semantic Proof of Generalised Cut Elimination for Deep Inference.

### Compositionality in constructing NbE frames

It appears possible to construct instances of several inductively
defined residualising functors using the cover modality. We do this by
first defining a covering relation and a membership relation for a
specific NbE model. For example, see
[Maybe.agda](/src/Instances/Maybe.agda) for an instance of the
residualising functor for the Maybe monad.

However, there is no support for "compositional construction" of these
functors. For example, suppose we wish to add sum types to the NbE
algorithm for the Maybe monad. What should we do?

We would need to extend the definition of the covering relation and
the membership relation manually and show that the expected properties
hold. However, this is clearly mechanical and we should be able to do
better.

One possible solution is to use a "description language" for defining
the covering relation. But what abou the membership relation?

```agda

import Context

module _
  (Ty  : Set)
  (_+_ : Ty → Ty → Ty)
  (let open Context Ty)
  (Ne : Ty → Ctx → Set)
  where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Product using (Σ; ∃ ; _×_ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥)

-- Cover Descriptor
data KD : Set₁ where
  const : (X : Ctx -> Set) -> KD
  ext   : (a : Ty) -> KD -> KD
  prod  : KD -> KD -> KD
  sum   : KD -> KD -> KD
  cexp  : (X : Ctx → Set) → KD → KD
  ex    : (Ty -> KD) -> KD
  top   : KD
  rec   : KD

⟦_⟧ : KD → (Ctx → Set) → (Ctx → Set)
⟦ const Y   ⟧ X Δ = Y Δ
⟦ ext a D   ⟧ X Δ = ⟦ D ⟧ X (Δ `, a)
⟦ prod D D' ⟧ X Δ = ⟦ D ⟧ X Δ × ⟦ D' ⟧ X Δ
⟦ sum D D'  ⟧ X Δ = ⟦ D ⟧ X Δ ⊎ ⟦ D' ⟧ X Δ
⟦ cexp Y D  ⟧ X Δ = Y Δ → ⟦ D ⟧ X Δ
⟦ ex Dₐ     ⟧ X Δ = Σ Ty λ a → ⟦ Dₐ a ⟧ X Δ
⟦ top       ⟧ X Δ = ⊤
⟦ rec       ⟧ X Δ = X Δ

data μ_ (D : KD) : Ctx → Set where
  lfp : {Γ : Ctx} → (⟦ D ⟧ (μ D)) Γ → (μ D) Γ

module Maybe where

   KDm : (Ctx → Set) → KD
   KDm A = sum
     top -- nothing
     (sum
       (const A) -- return/just
       (ex (λ a → prod (const (Ne a)) (ext a rec)))) -- letin 

   𝒞m : (Ctx → Set) → (Ctx → Set)
   𝒞m A = μ (KDm A)

   Km : Ctx → Set
   Km = 𝒞m (λ _ → ⊤)

   -- How should this be derived?
   _∈m_ : Ctx → {Γ : Ctx} → Km Γ → Set
   _∈m_ Δ {Γ} (lfp (inj₁ tt))                 = ⊥
   _∈m_ Δ {Γ} (lfp (inj₂ (inj₁ tt)))          = Γ ≡ Δ
   _∈m_ Δ {Γ} (lfp (inj₂ (inj₂ (a , n , k)))) = _∈m_ Δ k 
   
   -- 
   Coverm : (Ctx → Set) → Ctx → Set
   Coverm A Γ = Σ (Km Γ) λ k → ∀ {Δ} → Δ ∈m k → A Δ

   -- 
   to : {A : Ctx → Set} {Γ : Ctx} → 𝒞m A Γ → Coverm A Γ
   to (lfp (inj₁ tt))       = lfp (inj₁ tt) , λ ()
   to (lfp (inj₂ (inj₁ x))) = (lfp (inj₂ (inj₁ tt))) , λ { refl → x }
   to (lfp (inj₂ (inj₂ (a , n , m)))) = let (k , f) = to m in lfp (inj₂ (inj₂ (a , n , k))) , f  

   from : {A : Ctx → Set} {Γ : Ctx} → Coverm A Γ → 𝒞m A Γ
   from (k , f) = fromAux k f
     where
     fromAux : {A : Ctx → Set} {Γ : Ctx} (k : Km Γ) (f : ∀ {Δ} → Δ ∈m k → A Δ) → 𝒞m A Γ
     fromAux {A} (lfp (inj₁ tt))        f = lfp (inj₁ tt)
     fromAux {A} (lfp (inj₂ (inj₁ tt))) f = lfp (inj₂ (inj₁ (f refl)))
     fromAux {A} (lfp (inj₂ (inj₂ (a , n , k)))) f = lfp (inj₂ (inj₂ (a , n , fromAux k f)))
   
```


### Uniformity in implementing NbE (post model construction)

Currently the types of collect and register are not uniform when the
types are themselves not all functors in the object language. For
example, observe the differences here:

```agda
-- In AbelS19.agda
-- collect+ : Cover' (Nf' a) →̇ Nf' a
-- register+ : Ne' (a + b) →̇ Cover' (Ne' a ⊎' Ne' b)
--
-- In Maybe.agda
-- collectm : Cover' (Nf' a) →̇ Nf' (𝕞 a)
-- registerm : Ne' (𝕞 a) →̇ Cover' (Ne' a)
```

One way to unify the differences in register is to view both the type
connectives (and their semantics) as n-ary functors.

```agda
--
-- F+ : Ty → Ty → Ty
-- F+ a b = a + b
--
-- ℱ+ : USet → USet → USet
-- ℱ+ A B = Cover' (A ⊎ B)
--
--
-- Fm : Ty → Ty
-- Fm a = 𝕞 a
--
-- ℱ+ : USet → USet
-- ℱm A = Cover' A
--
-- the we have for AbelS19.agda:
-- register+ : Ne' (F+ a b) →̇ ℱ+ (Ne' a) (Ne' b)

-- and for Maybe.agda:
-- registerm : Ne' (Fm a) →̇ ℱm (Ne' a)
--
```

But what about the differences in collect? 
