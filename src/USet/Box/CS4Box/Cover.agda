{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Neighborhood.Systems as Sys
import USet.Localized as USetLoc

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

module USet.Box.CS4Box.Cover
  {W : Set} {_⊆_ : W → W → Set}
  (𝕎 : Preorder W _⊆_)
  (let open Sys 𝕎)
  {NS◻  : NeighborhoodSystem}
  (CS4BS : CS4BoxModalSystem NS◻)
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

open CS4BoxCover CS4BS
  renaming
    ( 𝒞'-distrib-×'-back to ◻'-distrib-×'-back
    ; 𝒞'-distrib-⊤'-back to ◻'-distrib-⊤'-back
    ; 𝒞'-pair to ◻'-pair
    ; extract' to ◻'-extract
    ; duplicate' to ◻'-duplicate
    )
  public

--
-- This module builds a "free" box modality
-- on localized upsets, as opposed to asking
-- for modal localization to be shown.
--
module FreeLocalizedCover
  {NS₊ : NeighborhoodSystem}
  (CS₊ : WeakCoverSystem NS₊)
  (let open NeighborhoodSystem NS₊ renaming (N to N₊ ; _∈_ to _∈◻_ ; refinement to refinement◻))
  (let open USetLoc 𝕎 CS₊)
  where

  open LUSet

  infix 21 ◻₊_
  
  ◻₊_ : LUSet → LUSet
  ◻₊ (luset A lA) = luset (𝒥' (◻' A)) (𝒥'-join {◻' A})

  ◻₊-map : {X Y : LUSet} → X →̇₊ Y → (◻₊ X) →̇₊ (◻₊ Y)
  ◻₊-map f = 𝒥'-map (◻'-map f) 

  ◻₊-distrib-×₊-forth : {X Y : LUSet} → ◻₊ (X ×₊ Y) →̇₊ ◻₊ X ×₊ ◻₊ Y
  ◻₊-distrib-×₊-forth {luset X _} {luset Y _} = →̇-trans
    (𝒥'-map (◻'-distrib-×'-forth {X} {Y}) )
    (𝒥'-distrib-×'-forth {◻' X} {◻' Y})

  ◻₊-distrib-×₊-back : {X Y : LUSet} →  ◻₊ X ×₊ ◻₊ Y →̇₊ ◻₊ (X ×₊ Y)
  ◻₊-distrib-×₊-back {luset X _} {luset Y _} = →̇-trans
    (𝒥'-distrib-×'-back {◻' X} {◻' Y})
    (𝒥'-map (◻'-distrib-×'-back {X} {Y}))

  ◻₊-distrib-⊤₊-back : ⊤₊ →̇₊ (◻₊ ⊤₊)
  ◻₊-distrib-⊤₊-back = →̇-trans 𝒥'-distrib-⊤'-back (𝒥'-map ◻'-distrib-⊤'-back)

  ◻₊-extract : {X : LUSet} → ◻₊ X →̇₊ X
  ◻₊-extract {luset X lX} = →̇-trans (𝒥'-map (◻'-extract {X})) lX

  ◻₊-duplicate : {X : LUSet} → ◻₊ X →̇₊ ◻₊ (◻₊ X) 
  ◻₊-duplicate {luset X lX} = →̇-trans
    (𝒥'-map (◻'-duplicate {X}))
    (𝒥'-map (◻'-map (𝒥'-point {◻' X})))

  ◻₊-pair : {G A B : LUSet} → G →̇₊ ◻₊ A → G →̇₊ ◻₊ B → G →̇₊ ◻₊ (A ×₊ B)
  ◻₊-pair {G} {A} {B} t u = ◻₊-distrib-×₊-back {A} {B} ∘' ⟨ t , u ⟩'
  
  open import HeytingAlgebras

  LUSetCKBoxA : CKBoxAlgebra
  LUSetCKBoxA = record
    { ℋ               = LUSetHA
    ; ◻_               = ◻₊_
    ; ◻-resp-≈         = λ { {X} {Y} (f , g) → 
      ( ◻₊-map {X} {Y} f , ◻₊-map {Y} {X} g ) }
    ; ◻-distrib-∧      = λ {X} {Y} →
      ( ◻₊-distrib-×₊-forth {X} {Y}
      , ◻₊-distrib-×₊-back {X} {Y}
      )
    ; ◻-distrib-⊤-back = ◻₊-distrib-⊤₊-back
    }

  LUSetCS4BoxA : CS4BoxAlgebra
  LUSetCS4BoxA = record
    { ckBoxAlgebra = LUSetCKBoxA
    ; ◻x≤x         = λ {X} → ◻₊-extract {X}
    ; ◻x≤◻◻x       = λ {X} → ◻₊-duplicate {X}
    }


