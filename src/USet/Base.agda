{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.CFrame as CF

module USet.Base
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (IF   : IFrame W _⊆_)
  (let open CF IF)
  (𝒦   : KPsh)
  (let open KPsh 𝒦)
  (_∈_ : (v : W) {w : W} → K w → Set)
  (let open Core 𝒦 _∈_)
  (CF : CFrame)
  where

open import Function using (id ; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-equiv)

open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; uncurry)

private
  variable
    w w' w'' u u' v v' : W

open IFrame IF
open CFrame CF

-- Upper set
record USet : Set₁ where
  constructor uset
  field
    Fam : W → Set
    wk  : w ⊆ w' → Fam w → Fam w'

open import Data.Sum

_×'_ : USet → USet → USet
(uset X wkX) ×' (uset Y wkY) = uset (λ w → X w × Y w) wk×
  where
  wk× : w ⊆ w' → X w × Y w → X w' × Y w'
  wk× i (x , y) = (wkX i x) , (wkY i y)

_⊎'_ : USet → USet → USet
(uset X wkX) ⊎' (uset Y wkY) = uset (λ w → X w ⊎ Y w) wk+
  where
  wk+ : w ⊆ w' → X w ⊎ Y w → X w' ⊎ Y w'
  wk+ i (inj₁ x) = inj₁ (wkX i x)
  wk+ i (inj₂ y) = inj₂ (wkY i y)

_→'_ : USet → USet → USet
(uset X wkX) →' (uset Y wkY) = uset (λ w → ∀ {w'} → w ⊆ w' → X w' → Y w') wk→
  where
  wk→ : {w w' : W} → w ⊆ w'
    → ({w1 : W} → w ⊆ w1 → X w1 → Y w1)
    → {w2 : W} → w' ⊆ w2 → X w2 → Y w2
  wk→ i f = λ i' x → f (⊆-trans i i') x

open USet renaming (Fam to _₀_) public

Cover' : USet → USet
Cover' A = uset CoverFam wkCov
  where
  CoverFam : W → Set
  CoverFam = λ w → Σ (K w) λ k → ForAllW k λ v → A ₀ v

  wkCov : w ⊆ w' → CoverFam w → CoverFam w'
  wkCov i (k , f) = wkK i k , λ p → wk A (factor⊆ i k p) (f (factor∈ i k p))

record _→̇_ (X Y : USet) : Set where
  constructor fun
  field
    apply : ∀ {w} → X ₀ w → Y ₀ w

open _→̇_ public

id' : {A : USet} → A →̇ A
id' .apply = id

_∘'_ : {A B C : USet} → B →̇ C → A →̇ B → A →̇ C
(f ∘' g) .apply = f .apply ∘ g .apply

inj₁' : {A B : USet} → A →̇ (A ⊎' B)
inj₁' .apply = inj₁

inj₂' : {A B : USet} → B →̇ (A ⊎' B)
inj₂' .apply = inj₂

[_,_]' : {A B C : USet} →  A →̇ C → B →̇ C → (A ⊎' B) →̇  C
[ f , g ]' .apply = [ f .apply , g .apply ]

mapCover' : {A B : USet} → (f : A →̇ B) → Cover' A →̇ Cover' B
mapCover' f .apply (k , g) = k , f .apply ∘ g

module _ {A B : USet} (run : {w : W} (k : K w) (f : ForAllW k (A ₀_)) → B ₀ w) where

  runCover : Cover' A →̇ B
  runCover .apply = uncurry run

module Return (PCF : Pointed CF) where
  open Pointed PCF

  return' : {A : USet} → A →̇ Cover' A
  return' {A} .apply {w} x = pointK[ w ] , λ v → subst (A ₀_) (point∈ v) x

module Join (JCF : Joinable CF) where
  open Joinable JCF

  join' : {A : USet} → Cover' (Cover' A) →̇ Cover' A
  join' {A} .apply {w} (k , f) = joinK k (proj₁ ∘ f) , λ e →
    let _ , e₁ , e₂ = join∈ k (proj₁ ∘ f) e
    in  f e₁ .proj₂ e₂

module Extract (CPCF : CoPointed CF) where
  open CoPointed CPCF

  extract' : {A : USet} → Cover' A →̇ A
  extract' {A} .apply {w} (k , f) = f (copoint∈ k)

module Cojoin (CJCF : CoJoinable CF) where
  open CoJoinable CJCF

  cojoin' : {A : USet} → Cover' A →̇ Cover' (Cover' A)
  cojoin' {A} .apply {w} (k , f) = k , λ p → cojoinK k p , λ p' → f (cojoin∈ k p p')
