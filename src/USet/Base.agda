{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.NFrame as NF

module USet.Base
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (𝕎   : Preorder W _⊆_)
  (let open NF 𝕎)
  (K   : W → Set)
  (_∈_ : (v : W) {w : W} → K w → Set)
  (let open Core K _∈_)
  (NF  : NFrame)
  where

open import Function using (id ; const ; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-equiv)

open import Data.Unit
open import Data.Sum
open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; uncurry)

private
  variable
    w w' w'' u u' v v' : W

open Preorder 𝕎
open NFrame NF

-- Upper set
record USet : Set₁ where
  constructor uset
  field
    Fam : W → Set
    wk  : w ⊆ w' → Fam w → Fam w'

⊤' : USet
⊤' = uset (const ⊤) _

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

  wkElems : {k : K w} {k' : K w'} → k ⊆k k' → ForAllW k (A ₀_) → ForAllW k' (A ₀_)
  wkElems is fam x = let (_ , x' , i) = is x in wk A i (fam x')

  wkCov : w ⊆ w' → CoverFam w → CoverFam w'
  wkCov i (k , f) = wkK i k , wkElems (wkK-resp-⊆ i k) f

record _→̇_ (X Y : USet) : Set where
  constructor fun
  field
    apply : ∀ {w} → X ₀ w → Y ₀ w

open _→̇_ public

id' : {A : USet} → A →̇ A
id' .apply = id

_∘'_ : {A B C : USet} → B →̇ C → A →̇ B → A →̇ C
(f ∘' g) .apply = f .apply ∘ g .apply

⟨_,_⟩' : {G A B : USet} → (G →̇ A) → (G →̇ B) → (G →̇ (A ×' B))
⟨ t , u ⟩' = fun λ g → t .apply g , u .apply g

proj₁' : {A B : USet} → (A ×' B) →̇ A
proj₁' .apply = proj₁

proj₂' : {A B : USet} → (A ×' B) →̇ B
proj₂' .apply = proj₂

lam' : {G A B : USet} → ((G ×' A) →̇ B) → G →̇ (A →' B)
lam' {G = G} f .apply g i a = f .apply ((wk G i g) , a)

app' : {G A B : USet} → G →̇ (A →' B) → G →̇ A → G →̇ B
app' t u .apply g = t .apply g ⊆-refl (u .apply g)

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

module Strength (PNF : Reachable NF) where
  open Reachable PNF

  strength' : {A B : USet} → (A ×' Cover' B) →̇ Cover' (A ×' B)
  strength' {A} .apply {w} (a , k , bs) = k , (λ {v} v∈k → (wk A (reachable k v∈k) a) , bs v∈k)
  
module Return (PNF : Pointed NF) where
  open Pointed PNF

  point' : {A : USet} → A →̇ Cover' A
  point' {A} .apply {w} x = pointK[ w ] , λ p → wk A (pointK-bwd-reachable p) x

  return' : {G A : USet} → G →̇ A → G →̇ Cover' A
  return' = point' ∘'_
  
module Join (JNF : Joinable NF) where
  open Joinable JNF

  join' : {A : USet} → Cover' (Cover' A) →̇ Cover' A
  join' {A} .apply {w} (k , h) = joinK k (proj₁ ∘ h) , λ {v'} v∈jN →
    let u , u∈k , v , v∈h- , v⊆v' = joinK-bwd-reachable k (proj₁ ∘ h) v∈jN
    in wk A v⊆v' (h u∈k .proj₂ v∈h-)

module Letin (PNF : Reachable NF) (JNF : Joinable NF) where
  open Strength PNF
  open Join JNF

  letin' : {G A B : USet} → (G →̇ Cover' A) → ((G ×' A) →̇ Cover' B) → (G →̇ Cover' B)
  letin' {G} {A} {B} t u = ((join' {B} ∘' mapCover' u) ∘' strength' {G} {A}) ∘' ⟨ id' , t ⟩' 
