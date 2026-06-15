{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Neighborhood.Systems as Sys
import USet.Localized as USetLoc

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

module USet.Lax.SL.Cover
  {W : Set} {_⊆_ : W → W → Set}
  (𝕎 : Preorder W _⊆_)
  (let open Sys 𝕎)
  {NS◇  : NeighborhoodSystem}
  (SLS◇ : SLModalSystem NS◇)
  where
  
open import USet.Base 𝕎
open NeighborhoodSystem NS◇ renaming
  (N to N◇ ; _∈_ to _∈◇_ ; refinement to refinement◇)
open SLModalSystem SLS◇ renaming
  (inclusion to inclusion◇)
open import USet.Cover 𝕎 NS◇
  renaming
    (𝒞' to ◇'
    ; map𝒞' to ◇'-map
    ; run𝒞' to ◇'-run
    ; 𝒞'-distrib-×'-forth to ◇'-distrib-×'-forth
    )
  public
  
open Strength inclusion◇
  renaming (strength' to ◇'-strength)
  public

module LocalizedCover
  {NS₊ : NeighborhoodSystem}
  (CS₊ : WeakCoverSystem NS₊)
  (let open NeighborhoodSystem NS₊ renaming (N to N₊ ; _∈_ to _∈₊_ ; refinement to refinement₊))
  (let open USetLoc 𝕎 CS₊)
  (◇'-localize : {A : USet} → 𝒥' (◇' A) →̇ ◇' (𝒥' A))
  where

  open LUSet

  ◇₊_ : LUSet → LUSet
  ◇₊ (luset A lA) = luset (◇' A) (◇'-map lA ∘' ◇'-localize {A})

  ◇₊-map : {X Y : LUSet} → X →̇₊ Y → (◇₊ X) →̇₊ (◇₊ Y)
  ◇₊-map = ◇'-map

  ◇₊-strength : {X Y : LUSet} → (X ×₊ (◇₊ Y)) →̇₊ (◇₊ (X ×₊ Y))
  ◇₊-strength {X} {Y} = ◇'-strength {X .𝒳} {Y .𝒳}
  
  open import HeytingAlgebras

  LUSetSLA : SLAlgebra
  LUSetSLA = record
    { ℋ          = LUSetHA
    ; ◇_          = ◇₊_
    ; ◇-resp-≈    = λ { {X} {Y} (f , g) → ◇₊-map {X} {Y} f , ◇₊-map {Y} {X} g }
      ; ◇x≤◇⟨x∨y⟩   = λ {X} {Y} → ◇₊-map {X} {X ⊎₊ Y} (inj₁₊ {X} {Y})
    ; x∧◇y≤◇⟨x∧y⟩ = λ {X} {Y} → ◇₊-strength {X} {Y}
    }
