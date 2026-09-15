{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Neighborhood.Systems as Sys
import USet.Localized as USetLoc

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

module USet.Lax.PLL.Relational
  {W : Set} {_⊑_ : W → W → Set}
  (𝕎i : Preorder W _⊑_)
  (let open Sys 𝕎i)
  -- For the lax modality
  {R     : (w v : W) → Set}
  (𝕎m    : Preorder W R)
  (R-incl : {w v : W} → R w v → w ⊑ v)
  (R-confluence : {w w' v : W} → w ⊑ w' → R w v → ∃ λ v' → R w' v' × (v ⊑ v'))
  where

open Preorder 𝕎m renaming
  ( ⊑-refl to R-refl
  ; ⊑-refl[_] to R-refl[_]
  ; ⊑-trans to R-trans
  )
open import USet.Base 𝕎i
  
private
  variable
    w w' w'' u u' v v' : W

infix 21 ⟨R⟩'_

-- Relational lax modality
⟨R⟩'_ : USet → USet
⟨R⟩' A = uset (λ w → ∃ λ v → R w v × A ₀ v) wkR
  where
  wkR : w ⊑ w' → ∃ (λ v → R w v × (A ₀ v)) → ∃ (λ v' → R w' v' × (A ₀ v'))
  wkR i (v , r , x) = let (v' , r' , i') = R-confluence i r in v' , r' , (wk A i' x)

⟨R⟩'-map : {A B : USet} → (f : A →̇ B) → ⟨R⟩' A →̇ ⟨R⟩' B
⟨R⟩'-map f .apply (v , r , x) = v , r , f .apply x

module LocalizedRelational
  {NS₊ : NeighborhoodSystem}
  (CS₊ : WeakCoverSystem NS₊)
  (let open NeighborhoodSystem NS₊ renaming (N to N₊ ; _∈_ to _∈₊_ ; refinement to refinement₊))
  (let open USetLoc 𝕎i CS₊)
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

  open import Neighborhood.Lib 𝕎i N◇ _∈◇_ renaming
    ( Refinement to Refinement◇
    ; Inclusion to Inclusion◇
    ; Identity to Identity◇
    ; Transitivity to Transitivity◇
    )

  refinement◇ : Refinement◇ 
  refinement◇ = record
    { wkN = λ i (v , r) →
      let (v' , r' , _) = R-confluence i r
      in v' , r'
    ; wkN-ref = λ { i (v , r) p →
      let (v' , r' , i') = R-confluence i r
      in v , ≡-refl , ≡-subst (v ⊑_) p i' }
    }

  inclusion◇ : Inclusion◇ 
  inclusion◇ = record { N-ref = λ (u , r) p → ≡-subst (_ ⊑_) p (R-incl r) }
  
  identity◇ : Identity◇
  identity◇ = record { idN[_] = λ w → w , R-refl[ w ] ; idN-sub = λ p → p }

  transitivity◇ : Transitivity◇
  transitivity◇ = record
    { transN     = λ {w} (u , r) h → let (v , r') = h ≡-refl in v , R-trans r r'
    ; transN-sub = λ {w} (u , r) h p → let (v , r') = h ≡-refl in (u , ≡-refl) , p
    }

  NS◇ : NeighborhoodSystem
  NS◇ = record { N = N◇ ; _∈_ = _∈◇_ ; refinement = refinement◇ }
  
  CS◇ : CoverSystem NS◇
  CS◇ = record
    { inclusion    = inclusion◇
    ; identity     = identity◇
    ; transitivity = transitivity◇
    }

  PLLS◇ : PLLModalSystem NS◇
  PLLS◇ = CoverSystem.weakCoverSystem CS◇

  open import USet.Lax.PLL.Cover 𝕎i PLLS◇ public

  ◇'-to-⟨R⟩' : {A : USet} → ◇' A →̇ ⟨R⟩' A
  ◇'-to-⟨R⟩' .apply ((v , r) , f) = v , r , f ≡-refl

  ⟨R⟩'-to-◇' : {A : USet} → ⟨R⟩' A →̇ ◇' A
  ⟨R⟩'-to-◇' {A} .apply (v , r , x) = (v , r) , λ p → ≡-subst (A ₀_) p x

  module LocalizedRelationalCover
    {NS₊ : NeighborhoodSystem}
    (CS₊ : WeakCoverSystem NS₊)
    (let open NeighborhoodSystem NS₊ renaming (N to N₊ ; _∈_ to _∈₊_ ; refinement to refinement₊))
    (let open USetLoc 𝕎i CS₊)
    (R-localize[_] : (A : USet) → 𝒥' (⟨R⟩' A) →̇ (⟨R⟩' 𝒥' A))
    where

    ◇'-localize[_] : (A : USet) → 𝒥' (◇' A) →̇ ◇' (𝒥' A)
    ◇'-localize[_] A = ⟨R⟩'-to-◇' {𝒥' A}
      ∘' (R-localize[ A ]
      ∘' 𝒥'-map (◇'-to-⟨R⟩' {A}))

    open LocalizedCover CS₊ (λ {A} → ◇'-localize[ A ]) public

    open LocalizedRelational CS₊ R-localize[_]

    ◇₊-to-⟨R⟩₊ : {A : LUSet} → (◇₊ A) →̇₊ (⟨R⟩₊ A)
    ◇₊-to-⟨R⟩₊ {luset A _} = ◇'-to-⟨R⟩' {A}

    ⟨R⟩₊-to-◇₊ : {A : LUSet} → (⟨R⟩₊ A) →̇₊ (◇₊ A)
    ⟨R⟩₊-to-◇₊ {luset A _} = ⟨R⟩'-to-◇' {A}
