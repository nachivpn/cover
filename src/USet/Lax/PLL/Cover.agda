{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.NFrame as NF
import USet.Localized as USetLoc

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

module USet.Lax.PLL.Cover
  {W     : Set}
  {_⊆_   : (w w' : W) → Set}
  (𝕎    : Preorder W _⊆_)
  {N◇    : W → Set}
  {_∈◇_  : (v : W) {w : W} → N◇ w → Set}
  (Nuc◇  : NF.Nuclear 𝕎 N◇ _∈◇_)
  where

open import USet.Base 𝕎

MNF◇  = Nuc◇ .NF.Nuclear.refinement
RNF◇  = Nuc◇ .NF.Nuclear.reachability
INF◇  = Nuc◇ .NF.Nuclear.identity
WINF◇ = NF.Identity.weakIdentity INF◇
TNF◇  = Nuc◇ .NF.Nuclear.transitivity
WTNF◇ = NF.Transitivity.weakTransitivity TNF◇

open import USet.Cover 𝕎 N◇ _∈◇_ MNF◇
  renaming
    (𝒞' to ◇'
    ; map𝒞' to ◇'-map
    ; run𝒞' to ◇'-run
    ; ×'-distr-forth' to ◇'-distrib-×'-forth
    )
  public

open StrongMonad RNF◇ WINF◇ WTNF◇
  renaming ( ×'-distr-back' to ◇'-distrib-×'-back
           ; join' to ◇'-join)
  public

module LocalizedCover
  {N₊   : W → Set}
  {_∈₊_ : (v : W) {w : W} → N₊ w → Set}
  (Nuc₊ : NF.Nuclear 𝕎 N₊ _∈₊_)
  (let open USetLoc 𝕎 N₊ _∈₊_ Nuc₊)
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
