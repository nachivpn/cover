{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Neighborhood.Systems as Sys
import USet.Localized as USetLoc

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

module USet.Lax.PLL.Cover
  {W : Set} {_⊆_ : W → W → Set}
  (𝕎 : Preorder W _⊆_)
  (let open Sys 𝕎)
  {NS◇   : NeighborhoodSystem}
  (PLLS◇ : PLLModalSystem NS◇)
  where

open import USet.Base 𝕎
open NeighborhoodSystem NS◇ renaming
  (N to N◇ ; _∈_ to _∈◇_ ; refinement to refinement◇)
open PLLModalSystem PLLS◇
open import USet.Cover 𝕎 NS◇
  renaming
    (𝒞' to ◇'
    ; map𝒞' to ◇'-map
    ; run𝒞' to ◇'-run
    ; 𝒞'-distrib-×'-forth to ◇'-distrib-×'-forth
    )
  public
  
open StrongMonad PLLS◇
  renaming ( 𝒞'-distrib-×'-back to ◇'-distrib-×'-back
           ; join' to ◇'-join)
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

  join₊ : {X : LUSet} → (◇₊ ◇₊ X) →̇₊ (◇₊ X)
  join₊ {X} = ◇'-join {𝒳 X}

  point₊ : {X : LUSet} → X →̇₊ (◇₊ X)
  point₊ {X} = point' {𝒳 X}

  ◇₊-distrib-×₊ : {X Y : LUSet}
    → (◇₊ (X ×₊ Y)) ↔̇₊ ((◇₊ X) ×₊ (◇₊ Y))
  ◇₊-distrib-×₊ {X} {Y} = ◇'-distrib-×'-forth {𝒳 X} {𝒳 Y} , ◇'-distrib-×'-back {𝒳 X} {𝒳 Y}

  open import HeytingAlgebras

  LUSetNuc : HasNucOp LUSetHA
  LUSetNuc = record
    { ◇_             = ◇₊_
    ; ◇-resp-≈       = λ { {X} {Y} (f , g) → ◇₊-map {X} {Y} f , ◇₊-map {Y} {X} g }
    ; x≤◇x           = λ {X} → point₊ {X}
    ; ◇◇x≤◇x         = λ {X} → join₊ {X}
    ; ◇-distrib-∧    = λ {X} {Y} → ◇₊-distrib-×₊ {X} {Y}
    }

  LUSetPLLA : PLLAlgebra
  LUSetPLLA = Properties.nucPLLAlgebra LUSetNuc

