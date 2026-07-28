{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
open import Neighborhood.FSPSystem

module SSet.JAlgebras
  {W : Set}
  (_⊲_ : W → (W → Set) → Set)
  {𝒮 : FSPSystem _⊲_}
  (let open FSPSystem 𝒮)
--  (𝒞 : CoherentFSPSystem _⊲_ 𝒮)
--  (let open CoherentFSPSystem 𝒞)
  where

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; uncurry)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open import SSet.Localized 𝒮 public

private
  η  = 𝒥'-point
  μ  = 𝒥'-join
  𝒿  = 𝒥'-map

η-natural :  {X Y : SSet} (f : X →̇ Y)
  → {w : W} (x : X w) → η {Y} (f x) ≡ 𝒿 f (η x)
η-natural f x = ≡-sym (⊲-iden-natural f x)

--
-- J-algebras
--

record IsJAlg (X : LSet) : Set where
  constructor jlag
  open LSet X renaming (localize to ℓ)
  
  field
    alg-unit   : {w : W} (x : 𝒳 w)
      → ℓ (η x) ≡ x
    alg-action : {w : W} (x : 𝒥' (𝒥' (𝒳)) w)
      → ℓ (μ x) ≡ ℓ (𝒿 ℓ x)

open IsJAlg

record IsJAlgHom {X Y : LSet} (f : X →̇₊ Y) : Set where

  open LSet X renaming (𝒳 to 𝒳ˣ ; localize to ℓˣ)
  open LSet Y renaming (𝒳 to 𝒳ʸ ; localize to ℓʸ)

  field
    alg-comm : {w : W} {x : 𝒥' 𝒳ˣ w}
      → f (ℓˣ x) ≡ ℓʸ (𝒥'-map f x)
open IsJAlgHom

⊤₊isJAlg : IsJAlg ⊤₊
⊤₊isJAlg = record
  { alg-unit   = λ {w} _ → ≡-refl
  ; alg-action = λ {w} _ → ≡-refl
  }

-- ⊥₊isJAlg : IsJAlg ⊥₊
-- ⊥₊isJAlg .alg-unit   = {!!}
-- ⊥₊isJAlg .alg-action = {!!}

open import Data.Sum

module _ {X Y : LSet} (P : IsJAlg X) (Q : IsJAlg Y) where

  open LSet X renaming (𝒳 to 𝒳ˣ ; localize to ℓˣ)
  open LSet Y renaming (𝒳 to 𝒳ʸ ; localize to ℓʸ)

  ⊎₊isJAlg : IsJAlg (X ⊎₊ Y)
  ⊎₊isJAlg .alg-unit   = {!!}
  ⊎₊isJAlg .alg-action = {!!}

  
  inj₁₊isJAlgHom : IsJAlgHom {X} {X ⊎₊ Y} (inj₁₊ {X} {Y})
  inj₁₊isJAlgHom .alg-comm {w} {x} = {!!}
