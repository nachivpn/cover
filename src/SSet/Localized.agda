{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
open import Neighborhood.FSPSystem

module SSet.Localized
  {W : Set}
  {_⊲_ : W → (W → Set) → Set}
  (𝒮 : FSPSystem _⊲_)
  (let open FSPSystem 𝒮)
  where

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

open import Relation.Binary.Lattice.Bundles using (BoundedLattice)
open import Relation.Binary.Lattice.Structures using (IsBoundedLattice)
open import Relation.Binary.Structures using (IsPreorder ; IsEquivalence)
open import Level using (0ℓ ; suc) ; private 1ℓ = suc 0ℓ

open import SSet.Base W public
open import SSet.Cover 𝒮 renaming
  ( 𝒞' to 𝒥'
  ; 𝒞'-map to 𝒥'-map
  ; point' to 𝒥'-point
  ; join' to 𝒥'-join
  ; return' to 𝒥'-return
  ) public 

private
  variable
    w w' w'' u u' v v' : W

-- Localized set
record LSet : Set₁ where
  constructor lset
  field
    𝒳 : SSet
    localize : 𝒥' 𝒳 →̇ 𝒳

-- Freely localize an arbitrary USet
FromUSet : SSet → LSet
FromUSet A = lset (𝒥' A) (𝒥'-join {A})

open LSet

--
-- Entailment
--

_→̇₊_ : LSet → LSet → Set
X →̇₊ Y = X .𝒳 →̇ Y .𝒳

→̇₊-refl = id'

→̇₊-trans : {A B C : LSet} → A →̇₊ B → B →̇₊ C → A →̇₊ C
→̇₊-trans = flip _∘'_

--
-- Truth
--

⊤₊ : LSet
⊤₊ = lset ⊤' (const tt)

--
-- Conjunction
--

_×₊_ : LSet → LSet → LSet
lset A lA ×₊ lset B lB = lset (A ×' B) localize-×'
  where
  localize-×' : 𝒥' (A ×' B) →̇ (A ×' B)
  localize-×' x = lA (𝒥'-map proj₁ x) , lB (𝒥'-map proj₂ x)
  
--
-- Falsity
--

⊥₊ : LSet
⊥₊ = FromUSet ⊥'

⊥₊-elim : {X : LSet} → ⊥₊ →̇₊ X
⊥₊-elim {X} = X. localize ∘ 𝒥'-map ⊥-elim

--
-- Disjunction
--
 
_⊎₊_ : LSet → LSet → LSet
lset A _ ⊎₊ lset B _  = FromUSet (A ⊎' B)

inj₁₊ : {X Y : LSet} → X →̇₊ (X ⊎₊ Y)
inj₁₊ {X} {Y} = 𝒥'-return inj₁

inj₂₊ : {X Y : LSet} → Y →̇₊ (X ⊎₊ Y)
inj₂₊ {X} {Y} = 𝒥'-return inj₂

[_,_]₊ : {X Y Z : LSet} →  X →̇₊ Z → Y →̇₊ Z → (X ⊎₊ Y) →̇₊ Z
[_,_]₊ {X} {Y} {Z} f g = Z .localize ∘ 𝒥'-map [ f , g ]

-- Note: observe the "localize after map𝒥" pattern
-- in ⊥₊-elim, [_,_]₊ and ×₊-distr-⊎₊-back.

--
-- Localized upper sets form a Heyting algebra
--

_↔̇₊_ : LSet → LSet → Set
A ↔̇₊ B = (A →̇₊ B) × (B →̇₊ A)

↔̇₊-isEquivalence : IsEquivalence _↔̇₊_
↔̇₊-isEquivalence = record
  { refl  = id , id
  ; sym   = λ p → (proj₂ p , proj₁ p)
  ; trans = λ p q → (q .proj₁ ∘ p .proj₁) , (p .proj₂ ∘ q .proj₂)
  }

↔̇₊-isPreorder : IsPreorder _↔̇₊_ _→̇₊_
↔̇₊-isPreorder = record
  { isEquivalence = ↔̇₊-isEquivalence
  ; reflexive     = proj₁
  ; trans         = →̇-trans
  }

LSetBLisBL : IsBoundedLattice _↔̇₊_ _→̇₊_ _⊎₊_ _×₊_ ⊤₊ ⊥₊
LSetBLisBL = record
    { isLattice = record
      { isPartialOrder = record
        { isPreorder = ↔̇₊-isPreorder
        ; antisym    = curry id
        }
      ; supremum = λ A B → inj₁₊ {A} {B} , inj₂₊ {A} {B} , λ C → [_,_]₊ {A} {B} {C}
      ; infimum = λ A B → proj₁ , proj₂ , λ C → ⟨_,_⟩' }
    ; maximum = λ A → unit' {A .𝒳}
    ; minimum = λ A → ⊥₊-elim {A}
    }

LSetBL : BoundedLattice 1ℓ 0ℓ 0ℓ
LSetBL = record
  { Carrier          = LSet
  ; _≈_              = _↔̇₊_
  ; _≤_              = _→̇₊_
  ; _∨_              = _⊎₊_
  ; _∧_              = _×₊_
  ; ⊤                = ⊤₊
  ; ⊥                = ⊥₊
  ; isBoundedLattice = LSetBLisBL
  }
