{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Neighborhood.Systems as Sys

module USet.Localized
  {W : Set} {_⊑_ : W → W → Set}
  (𝕎 : Preorder W _⊑_)
  (let open Sys 𝕎)
  {NS : NeighborhoodSystem}
  (let open NeighborhoodSystem NS)
  (CS : WeakCoverSystem NS)
  where

open WeakCoverSystem CS

open import Function using (id ; const ; _∘_ ; flip)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-equiv)

open import Data.Unit
open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)
open import Data.Empty
open import Data.Sum

open import Relation.Binary.Lattice.Bundles using (HeytingAlgebra)
open import Relation.Binary.Lattice.Structures using (IsHeytingAlgebra)
open import Relation.Binary.Structures using (IsPreorder ; IsEquivalence)
open import Level using (0ℓ ; suc) ; private 1ℓ = suc 0ℓ

open import USet.Base 𝕎
open import USet.Cover 𝕎 NS renaming
  ( 𝒞' to 𝒥'
  ; map𝒞' to map𝒥'
  ; run𝒞' to run𝒥'
  ) public 

private
  variable
    w w' w'' u u' v v' : W

open StrongMonad CS
  renaming ( point' to 𝒥'-point
           ; join' to 𝒥'-join
           )
  public

-- Localized upper set
record LUSet : Set₁ where
  constructor luset

  -- upper set
  field
    𝒳 : USet

  open USet 𝒳

  -- localization property
  field
    localize : 𝒥' 𝒳 →̇ 𝒳

-- Freely localize an arbitrary USet
FromUSet : USet → LUSet
FromUSet A = luset (𝒥' A) (𝒥'-join {A})

open LUSet

wk₊ : (X : LUSet) → w ⊑ w' → X .𝒳 ₀ w → X .𝒳 ₀ w'
wk₊ X = wk (X .𝒳)

--
-- Entailment
--

_→̇₊_ : LUSet → LUSet → Set
X →̇₊ Y = X .𝒳 →̇ Y .𝒳

→̇₊-refl = id'

→̇₊-trans : {A B C : LUSet} → A →̇₊ B → B →̇₊ C → A →̇₊ C
→̇₊-trans = flip _∘'_

--
-- Truth
--

⊤₊ : LUSet
⊤₊ = luset ⊤' (fun (const tt))

--
-- Conjunction
--

_×₊_ : LUSet → LUSet → LUSet
luset A lA ×₊ luset B lB = luset (A ×' B) localize-×'
  where
  localize-×' : 𝒥' (A ×' B) →̇ (A ×' B)
  localize-×' = (lA ×'-map lB) ∘' 𝒞'-distrib-×'-forth {A} {B}

--
-- Implication/Exponential
--

_→₊_ : LUSet → LUSet → LUSet
luset A lA →₊ luset B lB = luset (A →' B) localize-→'
  where
  localize-→' : 𝒥' (A →' B) →̇ (A →' B)
  localize-→' = lam' (lB
    ∘' (map𝒥' {(A →' B) ×' A} {B} eval'
    ∘' swapped-strength' {A →' B} {A}))

--
-- Falsity
--

⊥₊ : LUSet
⊥₊ = FromUSet ⊥'

⊥₊-elim : {X : LUSet} → ⊥₊ →̇₊ X
⊥₊-elim {X} = X .localize ∘' map𝒥' {⊥'} {X .𝒳} ⊥'-elim

--
-- Disjunction
--
 
_⊎₊_ : LUSet → LUSet → LUSet
luset A _ ⊎₊ luset B _  = FromUSet (A ⊎' B)

inj₁₊ : {X Y : LUSet} → X →̇₊ (X ⊎₊ Y)
inj₁₊ {X} {Y} = return' {X .𝒳} {X .𝒳 ⊎' Y .𝒳} inj₁'

inj₂₊ : {X Y : LUSet} → Y →̇₊ (X ⊎₊ Y)
inj₂₊ {X} {Y} = return' {Y .𝒳} {X .𝒳 ⊎' Y .𝒳} inj₂'

[_,_]₊ : {X Y Z : LUSet} →  X →̇₊ Z → Y →̇₊ Z → (X ⊎₊ Y) →̇₊ Z
[_,_]₊ {X} {Y} {Z} f g = Z .localize ∘' map𝒥' {X .𝒳 ⊎' Y .𝒳} {Z .𝒳} [ f , g ]'

--
-- Distributivity (of conjunction over disjunction)
--

×₊-distr-⊎₊-forth : {X Y Z : LUSet} → (X ×₊ (Y ⊎₊ Z)) →̇₊ ((X ×₊ Y) ⊎₊ (X ×₊ Z))
×₊-distr-⊎₊-forth {luset A lA} {luset B lB} {luset C lC} =
  map𝒥' {A ×' (B ⊎' C)} {(A ×' B) ⊎' (A ×' C)}  ×'-distr-⊎'-forth
  ∘' strength' {A} {B ⊎' C}

×₊-distr-⊎₊-back : {X Y Z : LUSet} → ((X ×₊ Y) ⊎₊ (X ×₊ Z)) →̇₊ (X ×₊ (Y ⊎₊ Z))
×₊-distr-⊎₊-back X@{luset A lA} Y@{luset B lB} Z@{luset C lC} =
  (X ×₊ (Y ⊎₊ Z)) .localize
  ∘' (map𝒥' {(A ×' B) ⊎' (A ×' C)} {A ×' 𝒥' (B ⊎' C)}
            ((id' ×'-map return' id')
            ∘' ×'-distr-⊎'-back))

-- Note: observe the "localize after map𝒥" pattern
-- in ⊥₊-elim, [_,_]₊ and ×₊-distr-⊎₊-back.

--
-- Localized upper sets form a Heyting algebra
--

_↔̇₊_ : LUSet → LUSet → Set
A ↔̇₊ B = (A →̇₊ B) × (B →̇₊ A)

↔̇₊-isEquivalence : IsEquivalence _↔̇₊_
↔̇₊-isEquivalence = record
  { refl  = →̇-refl , →̇-refl
  ; sym   = λ p → (proj₂ p , proj₁ p)
  ; trans = λ p q → →̇-trans (proj₁ p) (proj₁ q) , →̇-trans (proj₂ q) (proj₂ p)
  }

↔̇₊-isPreorder : IsPreorder _↔̇₊_ _→̇₊_
↔̇₊-isPreorder = record
  { isEquivalence = ↔̇₊-isEquivalence
  ; reflexive     = proj₁
  ; trans         = →̇-trans
  }

LUSetHAisHA : IsHeytingAlgebra _↔̇₊_ _→̇₊_ _⊎₊_ _×₊_ _→₊_ ⊤₊ ⊥₊
LUSetHAisHA = record
  { isBoundedLattice = record
    { isLattice = record
      { isPartialOrder = record
        { isPreorder = ↔̇₊-isPreorder
        ; antisym    = curry id
        }
      ; supremum = λ A B → inj₁₊ {A} {B} , inj₂₊ {A} {B} , λ C → [_,_]₊ {A} {B} {C}
      ; infimum = λ A B → proj₁' , proj₂' , λ C → ⟨_,_⟩' }
    ; maximum = λ _ → unit'
    ; minimum = λ A → ⊥₊-elim {A}
    }
  ; exponential = λ G A B → curry' , uncurry'
  }
  
LUSetHA : HeytingAlgebra 1ℓ 0ℓ 0ℓ
LUSetHA = record
  { Carrier          = LUSet
  ; _≈_              = _↔̇₊_
  ; _≤_              = _→̇₊_
  ; _∨_              = _⊎₊_
  ; _∧_              = _×₊_
  ; _⇨_              = _→₊_
  ; ⊤                = ⊤₊
  ; ⊥                = ⊥₊
  ; isHeytingAlgebra = LUSetHAisHA
  }
