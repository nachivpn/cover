{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Neighborhood.Systems as Sys
import USet.Localized as USetLoc

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

module USet.Box.CKBox.Cover
  {W : Set} {_⊆_ : W → W → Set}
  (𝕎 : Preorder W _⊆_)
  (let open Sys 𝕎)
  {NS◻  : NeighborhoodSystem}
  (CKS◻ : CKBoxModalSystem NS◻)
  where

open import USet.Base 𝕎

open NeighborhoodSystem NS◻ renaming
  (N to N◻ ; _∈_ to _∈◻_ ; refinement to refinement◻)
 
open import USet.Cover 𝕎 NS◻
  renaming
    ( 𝒞' to ◻'
    ; map𝒞' to ◻'-map
    ; run𝒞' to ◻'-run
    ; 𝒞'-distrib-×'-forth to ◻'-distrib-×'-forth
    )
  public

open CKBoxCover CKS◻
  renaming
    ( 𝒞'-distrib-×'-back to ◻'-distrib-×'-back
    ; 𝒞'-distrib-⊤'-back to ◻'-distrib-⊤'-back
    ; 𝒞'-pair to ◻'-pair
    )
  public

module LocalizedCover
  {NS₊ : NeighborhoodSystem}
  (CS₊ : WeakCoverSystem NS₊)
  (let open NeighborhoodSystem NS₊ renaming (N to N₊ ; _∈_ to _∈◻_ ; refinement to refinement◻))
  (let open USetLoc 𝕎 CS₊)
  (◻'-localize : {A : USet} → 𝒥' (◻' A) →̇ ◻' (𝒥' A))
  where

  open LUSet

  ◻₊_ : LUSet → LUSet
  ◻₊ (luset A lA) = luset (◻' A) (◻'-map lA ∘' ◻'-localize {A})

  ◻₊-map : {X Y : LUSet} → X →̇₊ Y → (◻₊ X) →̇₊ (◻₊ Y)
  ◻₊-map = ◻'-map

  open import HeytingAlgebras

  LUSetCKBoxA : CKBoxAlgebra
  LUSetCKBoxA = record
    { ℋ               = LUSetHA
    ; ◻_               = ◻₊_
    ; ◻-resp-≈         = λ { {X} {Y} (f , g) → 
      ( ◻₊-map {X} {Y} f , ◻₊-map {Y} {X} g ) }
    ; ◻-distrib-∧      = λ {X} {Y} →
      ( ◻'-distrib-×'-forth {X .𝒳} {Y .𝒳}
      , ◻'-distrib-×'-back {X .𝒳} {Y .𝒳}
      )
    ; ◻-distrib-⊤-back = ◻'-distrib-⊤'-back
    }

