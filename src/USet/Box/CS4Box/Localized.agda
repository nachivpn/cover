{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Neighborhood.Systems as Sys

module USet.Box.CS4Box.Localized
  {W : Set} {_⊑_ : W → W → Set}
  (𝕎 : Preorder W _⊑_)
  (let open Sys 𝕎)
  {NS : NeighborhoodSystem}
  (let open NeighborhoodSystem NS)
  (DS : IntSystem NS)
  where

open IntSystem DS

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
  ( 𝒞' to ℱ'
  ; map𝒞' to mapℱ'
  ; run𝒞' to runℱ'
  ; 𝒞'-distrib-×'-forth to ℱ'-distrib-×'-forth
  ) public 

private
  variable
    w w' w'' u u' v v' : W

open Extract density renaming (extract' to ℱ'-extract) public

-- Deflating upper sets
record DUset : Set₁ where
  constructor luset

  -- upper set
  field
    𝒳 : USet

  open USet 𝒳

  -- deflating property
  field
    deflate : ℱ' 𝒳 →̇ 𝒳

open DUset

wk◻ : (X : DUset) → w ⊑ w' → X .𝒳 ₀ w → X .𝒳 ₀ w'
wk◻ X = wk (X .𝒳)

--
-- Entailment
--

_→̇◻_ : DUset → DUset → Set
X →̇◻ Y = X .𝒳 →̇ Y .𝒳

→̇◻-refl = id'

→̇◻-trans : {A B C : DUset} → A →̇◻ B → B →̇◻ C → A →̇◻ C
→̇◻-trans = flip _∘'_

--
-- Truth
--

⊤◻ : DUset
⊤◻ = luset ⊤' (fun (const tt))

--
-- Conjunction
--

_×◻_ : DUset → DUset → DUset
luset A lA ×◻ luset B lB = luset (A ×' B) deflate-×'
  where
  deflate-×' : ℱ' (A ×' B) →̇ (A ×' B)
  deflate-×' = (lA ×'-map lB) ∘' ℱ'-distrib-×'-forth {A} {B}

--
-- Implication/Exponential
--

_→◻_ : DUset → DUset → DUset
luset A lA →◻ luset B lB = luset (A →' B) deflate-→'
  where
  deflate-→' : ℱ' (A →' B) →̇ (A →' B)
  deflate-→' = {!!}


{-
--
-- Falsity
--

⊥◻ : DUset
⊥◻ = FromUSet ⊥'

⊥◻-elim : {X : DUset} → ⊥◻ →̇◻ X
⊥◻-elim {X} = X .deflate ∘' mapℱ' {⊥'} {X .𝒳} ⊥'-elim

--
-- Disjunction
--
 
_⊎◻_ : DUset → DUset → DUset
luset A _ ⊎◻ luset B _  = FromUSet (A ⊎' B)

inj₁◻ : {X Y : DUset} → X →̇◻ (X ⊎◻ Y)
inj₁◻ {X} {Y} = return' {X .𝒳} {X .𝒳 ⊎' Y .𝒳} inj₁'

inj₂◻ : {X Y : DUset} → Y →̇◻ (X ⊎◻ Y)
inj₂◻ {X} {Y} = return' {Y .𝒳} {X .𝒳 ⊎' Y .𝒳} inj₂'

[_,_]◻ : {X Y Z : DUset} →  X →̇◻ Z → Y →̇◻ Z → (X ⊎◻ Y) →̇◻ Z
[_,_]◻ {X} {Y} {Z} f g = Z .deflate ∘' mapℱ' {X .𝒳 ⊎' Y .𝒳} {Z .𝒳} [ f , g ]'

--
-- Distributivity (of conjunction over disjunction)
--

×◻-distr-⊎◻-forth : {X Y Z : DUset} → (X ×◻ (Y ⊎◻ Z)) →̇◻ ((X ×◻ Y) ⊎◻ (X ×◻ Z))
×◻-distr-⊎◻-forth {luset A lA} {luset B lB} {luset C lC} =
  mapℱ' {A ×' (B ⊎' C)} {(A ×' B) ⊎' (A ×' C)}  ×'-distr-⊎'-forth
  ∘' strength' {A} {B ⊎' C}

×◻-distr-⊎◻-back : {X Y Z : DUset} → ((X ×◻ Y) ⊎◻ (X ×◻ Z)) →̇◻ (X ×◻ (Y ⊎◻ Z))
×◻-distr-⊎◻-back X@{luset A lA} Y@{luset B lB} Z@{luset C lC} =
  (X ×◻ (Y ⊎◻ Z)) .deflate
  ∘' (mapℱ' {(A ×' B) ⊎' (A ×' C)} {A ×' ℱ' (B ⊎' C)}
            ((id' ×'-map return' id')
            ∘' ×'-distr-⊎'-back))

-- Note: observe the "deflate after mapℱ" pattern
-- in ⊥◻-elim, [_,_]◻ and ×◻-distr-⊎◻-back.

--
-- Deflated upper sets form a Heyting algebra
--

_↔̇◻_ : DUset → DUset → Set
A ↔̇◻ B = (A →̇◻ B) × (B →̇◻ A)

↔̇◻-isEquivalence : IsEquivalence _↔̇◻_
↔̇◻-isEquivalence = record
  { refl  = →̇-refl , →̇-refl
  ; sym   = λ p → (proj₂ p , proj₁ p)
  ; trans = λ p q → →̇-trans (proj₁ p) (proj₁ q) , →̇-trans (proj₂ q) (proj₂ p)
  }

↔̇◻-isPreorder : IsPreorder _↔̇◻_ _→̇◻_
↔̇◻-isPreorder = record
  { isEquivalence = ↔̇◻-isEquivalence
  ; reflexive     = proj₁
  ; trans         = →̇-trans
  }

DUsetHAisHA : IsHeytingAlgebra _↔̇◻_ _→̇◻_ _⊎◻_ _×◻_ _→◻_ ⊤◻ ⊥◻
DUsetHAisHA = record
  { isBoundedLattice = record
    { isLattice = record
      { isPartialOrder = record
        { isPreorder = ↔̇◻-isPreorder
        ; antisym    = curry id
        }
      ; supremum = λ A B → inj₁◻ {A} {B} , inj₂◻ {A} {B} , λ C → [_,_]◻ {A} {B} {C}
      ; infimum = λ A B → proj₁' , proj₂' , λ C → ⟨_,_⟩' }
    ; maximum = λ _ → unit'
    ; minimum = λ A → ⊥◻-elim {A}
    }
  ; exponential = λ G A B → curry' , uncurry'
  }
  
DUsetHA : HeytingAlgebra 1ℓ 0ℓ 0ℓ
DUsetHA = record
  { Carrier          = DUset
  ; _≈_              = _↔̇◻_
  ; _≤_              = _→̇◻_
  ; _∨_              = _⊎◻_
  ; _∧_              = _×◻_
  ; _⇨_              = _→◻_
  ; ⊤                = ⊤◻
  ; ⊥                = ⊥◻
  ; isHeytingAlgebra = DUsetHAisHA
  }
-}
