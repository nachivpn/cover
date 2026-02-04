{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.NFrame as NF
import USet.Localized as USetLoc

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

module USet.Box.CKBox.Cover
  {W     : Set}
  {_⊆_   : (w w' : W) → Set}
  (𝕎    : Preorder W _⊆_)
  {N◻    : W → Set}
  {_∈◻_  : (v : W) {w : W} → N◻ w → Set}
  (Mon◻  : NF.MonoidalFrame 𝕎 N◻ _∈◻_)
  where

open import USet.Base 𝕎

RNF◻ = Mon◻ .NF.MonoidalFrame.refinement
MNF◻ = Mon◻ .NF.MonoidalFrame.multiplicativity
UNF◻ = Mon◻ .NF.MonoidalFrame.unitality

open import USet.Cover 𝕎 N◻ _∈◻_ RNF◻
  renaming
    ( 𝒞' to ◻'
    ; map𝒞' to ◻'-map
    ; run𝒞' to ◻'-run
    ; 𝒞'-distrib-×'-forth to ◻'-distrib-×'-forth
    )
  public

open Monoidal MNF◻ UNF◻
  renaming
    ( 𝒞'-distrib-×'-back to ◻'-distrib-×'-back
    ; 𝒞'-distrib-⊤'-back to ◻'-distrib-⊤'-back
    )
  public

module LocalizedCover
  {N₊   : W → Set}
  {_∈₊_ : (v : W) {w : W} → N₊ w → Set}
  (Nuc₊ : NF.NuclearFrame 𝕎 N₊ _∈₊_)
  (let open USetLoc 𝕎 N₊ _∈₊_ Nuc₊)
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
