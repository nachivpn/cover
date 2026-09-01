{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.STPC.Semantics.Categorical where

open import Init

open import Categories.Category.Cartesian 
open import Categories.Category.Cocartesian

open import Instances.LatLog.STPC.Calculus
open import Instances.LatLog.STPC.Conversion

record STPCModel : Set₁ where

  field
    𝒞             : Category
    𝒞-cartesian   : Cartesian 𝒞
    𝒞-cocartesian : Cocartesian 𝒞

  module 𝒞 = Category 𝒞
  open 𝒞 renaming (_≈_ to _≋_ ; _⇒_ to _∼>_) public
  open Equiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans) public 
  open Cartesian 𝒞-cartesian renaming (⊤ to 𝟙' ; _×_ to _×'_ ; unique to ×'-unique) public
  open Cocartesian 𝒞-cocartesian
    renaming (⊥ to 𝟘' ; _+_ to _＋'_ ; +-unique to ＋'-unique ; +-η to +'-η) public

  field
    Vι : Atom → Obj

module Interpretation (ℳ : STPCModel) where

  open STPCModel ℳ public
  
  ⟦_⟧ : Ty → Obj
  ⟦ 𝕡 x ⟧   = Vι x
  ⟦ 𝟙 ⟧     = 𝟙'
  ⟦ 𝟘 ⟧     = 𝟘'
  ⟦ a × b ⟧ = ⟦ a ⟧ ×' ⟦ b ⟧
  ⟦ a ＋ b ⟧ = ⟦ a ⟧ ＋' ⟦ b ⟧
  
  ⟦_⟧ᶜ : Ctx → Obj
  ⟦ [] ⟧ᶜ     = 𝟙'
  ⟦ Γ `, a ⟧ᶜ = ⟦ Γ ⟧ᶜ ×' ⟦ a ⟧

  evalVar : Var Γ a → ⟦ Γ ⟧ᶜ ∼> ⟦ a ⟧
  evalVar v0       = π₂
  evalVar (succ x) = evalVar x ∘ π₁
  
  eval : Tm Γ a → ⟦ Γ ⟧ᶜ ∼> ⟦ a ⟧
  eval (var x)         = evalVar x
  eval unit            = !
  eval (abort t)       = ¡ ∘ eval t
  eval (pair t u)      = ⟨ eval t , eval u ⟩
  eval (fst t)         = π₁ ∘ eval t
  eval (snd t)         = π₂ ∘ eval t
  eval (inl t)         = i₁ ∘ eval t
  eval (inr t)         = i₂ ∘ eval t
  eval (match s t₁ t₂) = [ eval t₁ ∘ ⟨ ! , id ⟩ , eval t₂ ∘ ⟨ ! , id ⟩ ] ∘ eval s

_≈[_]_ : Tm Γ a → STPCModel → Tm Γ a → Set
t ≈[ ℳ ] u = let open Interpretation ℳ in eval t ≋ eval u

CategoricalSoundness : Set₁
CategoricalSoundness = {Γ : Ctx} {a : Ty} (t u : Tm Γ a)
  → t ≈ u
  → (∀ ℳ → t ≈[ ℳ ] u)

CategoricalCompleteness : Set₁
CategoricalCompleteness = {Γ : Ctx} {a : Ty} (t u : Tm Γ a)
  → (∀ ℳ → t ≈[ ℳ ] u)
  → t ≈ u
