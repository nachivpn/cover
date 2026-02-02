{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.NFrame as NF
import USet.Localized as USetLoc

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

module USet.Lax.Relational
  {W     : Set}
  {_⊆_   : (w w' : W) → Set}
  {R     : (w v : W) → Set}
  (𝕎i    : Preorder W _⊆_)
  -- For the lax modality
  (𝕎m    : Preorder W R)
  (R-incl : {w v : W} → R w v → w ⊆ v)
  (R-confluence : {w w' v : W} → w ⊆ w' → R w v → ∃ λ v' → R w' v' × (v ⊆ v'))
  where

open Preorder 𝕎m renaming
  ( ⊆-refl to R-refl
  ; ⊆-refl[_] to R-refl[_]
  ; ⊆-trans to R-trans
  )
open import USet.Base 𝕎i

private
  variable
    w w' w'' u u' v v' : W

infix 21 ⟨R⟩'_

-- Lax modality
⟨R⟩'_ : USet → USet
⟨R⟩' A = uset (λ w → ∃ λ v → R w v × A ₀ v) wkR
  where
  wkR : w ⊆ w' → ∃ (λ v → R w v × (A ₀ v)) → ∃ (λ v' → R w' v' × (A ₀ v'))
  wkR i (v , r , x) = let (v' , r' , i') = R-confluence i r in v' , r' , (wk A i' x)

⟨R⟩'-map : {A B : USet} → (f : A →̇ B) → ⟨R⟩' A →̇ ⟨R⟩' B
⟨R⟩'-map f .apply (v , r , x) = v , r , f .apply x

module LocalizedRelational
  (N   : W → Set)
  (_∈_ : (v : W) {w : W} → N w → Set)
  (let open NF 𝕎i N _∈_)
  (Nuc  : Nuclear)
  (let open USetLoc 𝕎i N _∈_ Nuc)
  (R-localize[_] : (A : USet) → 𝒥' (⟨R⟩' A) →̇ (⟨R⟩' 𝒥' A))
  where

  open LUSet

  ⟨R⟩₊_ : LUSet → LUSet
  ⟨R⟩₊ (luset A lA) = luset (⟨R⟩' A) (⟨R⟩'-map lA ∘' R-localize[ A ])

module RelationalCover
  where

  open import Relation.Binary.PropositionalEquality
    using (_≡_)
    renaming (refl to ≡-refl ; subst to ≡-subst)

  N◇ : W → Set
  N◇ w = Σ W (R w)

  _∈◇_  : (v : W) {w : W} → N◇ w → Set
  v ∈◇ (u , _) = u ≡ v

  MNF : NF.Refinement 𝕎i N◇ _∈◇_
  MNF = record
    { wkN = λ i (v , r) →
      let (v' , r' , _) = R-confluence i r
      in v' , r'
    ; wkN-refines = λ { i (v , r) p →
      let (v' , r' , i') = R-confluence i r
      in v , ≡-refl , ≡-subst (v ⊆_) p i' }
    }

  RNF : NF.Reachability 𝕎i N◇ _∈◇_
  RNF = record { reachable = λ (u , r) p → ≡-subst (_ ⊆_) p (R-incl r) }

  INF : NF.Identity 𝕎i N◇ _∈◇_
  INF = record { idN[_] = λ w → w , R-refl[ w ] ; idN-bwd-member = λ p → p }

  TNF : NF.Transitivity 𝕎i N◇ _∈◇_
  TNF = record
    { transN            = λ {w} (u , r) h → let (v , r') = h ≡-refl in v , R-trans r r'
    ; transN-bwd-member = λ {w} (u , r) h p → let (v , r') = h ≡-refl in u , ≡-refl , p
    }

  Nuc◇ : NF.Nuclear 𝕎i N◇ _∈◇_
  Nuc◇ = record
    { refinement   = MNF
    ; reachability = RNF
    ; identity     = INF
    ; transitivity = TNF
    }

  open import USet.Lax.Cover 𝕎i Nuc◇ public

  ◇'-to-⟨R⟩' : {A : USet} → ◇' A →̇ ⟨R⟩' A
  ◇'-to-⟨R⟩' .apply ((v , r) , f) = v , r , f ≡-refl

  ⟨R⟩'-to-◇' : {A : USet} → ⟨R⟩' A →̇ ◇' A
  ⟨R⟩'-to-◇' {A} .apply (v , r , x) = (v , r) , λ p → ≡-subst (A ₀_) p x

  module LocalizedRelationalCover
    (N₊   : W → Set)
    (_∈₊_ : (v : W) {w : W} → N₊ w → Set)
    (Nuc₊ : NF.Nuclear 𝕎i N₊ _∈₊_)
    (let open USetLoc 𝕎i N₊ _∈₊_ Nuc₊)
    (R-localize[_] : (A : USet) → 𝒥' (⟨R⟩' A) →̇ (⟨R⟩' 𝒥' A))
    where

    ◇'-localize[_] : (A : USet) → 𝒥' (◇' A) →̇ ◇' (𝒥' A)
    ◇'-localize[_] A = ⟨R⟩'-to-◇' {𝒥' A}
      ∘' (R-localize[ A ]
      ∘' map𝒥' (◇'-to-⟨R⟩' {A}))

    open LocalizedCover Nuc₊ (λ {A} → ◇'-localize[ A ]) public

    open LocalizedRelational N₊ _∈₊_ Nuc₊ R-localize[_]

    ◇₊-to-⟨R⟩₊ : {A : LUSet} → (◇₊ A) →̇₊ (⟨R⟩₊ A)
    ◇₊-to-⟨R⟩₊ {luset A _} = ◇'-to-⟨R⟩' {A}

    ⟨R⟩₊-to-◇₊ : {A : LUSet} → (⟨R⟩₊ A) →̇₊ (◇₊ A)
    ⟨R⟩₊-to-◇₊ {luset A _} = ⟨R⟩'-to-◇' {A}
