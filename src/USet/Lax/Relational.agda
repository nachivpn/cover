{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.NFrame as NF

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; curry ; uncurry)

module USet.Lax.Relational
  {W     : Set}
  {_⊆_   : (w w' : W) → Set}
  {R     : (w v : W) → Set}
  (𝕎i    : Preorder W _⊆_)
  -- For the lax modality
  (𝕎m    : Preorder W R)
  (R-confluence : {w w' v : W} → w ⊆ w' → R w v → ∃ λ v' → R w' v' × (v ⊆ v'))
  where

open import USet.Base 𝕎i

private
  variable
    w w' w'' u u' v v' : W

infix 21 ⟨R⟩'_

⟨R⟩'_ : USet → USet
⟨R⟩' A = uset (λ w → ∃ λ v → R w v × A ₀ v) wkR
  where
  wkR : w ⊆ w' → ∃ (λ v → R w v × (A ₀ v)) → ∃ (λ v' → R w' v' × (A ₀ v'))
  wkR i (v , r , x) = let (v' , r' , i') = R-confluence i r in v' , r' , (wk A i' x)

module Localized
  (N   : W → Set)
  (_∈_ : (v : W) {w : W} → N w → Set)
  (let open NF 𝕎i N _∈_)
  (Nuc  : Nuclear)
  (R-localize : {A : USet} {w : W}
    → (n : N w) → ForAllW n (⟨R⟩' A ₀_)
    → ∃ λ u → R w u × Σ (N u) (AllForW (A ₀_)))
  where

  open import USet.Localized 𝕎i N _∈_ Nuc

  open LUSet

  ⟨R⟩₊_ : LUSet → LUSet
  ⟨R⟩₊ (luset A lA) = luset (⟨R⟩' A) localizeR
    where
    localizeR : 𝒞' (⟨R⟩' A) →̇ ⟨R⟩' A
    localizeR .apply (n , h) =
      let (u , r , cA) = R-localize {A} n h
      in u , r , lA .apply cA
