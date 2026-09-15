{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Neighborhood.Systems as Sys

module USet.Cover
  {W : Set} {_⊑_ : W → W → Set}
  (𝕎 : Preorder W _⊑_)
  (let open Sys 𝕎)
  (NS : NeighborhoodSystem)
  where

open NeighborhoodSystem NS
open import Function using (id ; const ; _∘_)

--open import Data.Unit
open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; uncurry)
open import Data.Empty
--open import Data.Sum

--open System RNF

private
  variable
    w w' w'' u u' v v' : W

open import USet.Base 𝕎

-- Cover modality
𝒞' : USet → USet
𝒞' A = uset CoverFam wkCov
  where
  CoverFam : W → Set
  CoverFam = λ w → Σ (N w) λ n → ForAllW n λ v → A ₀ v

  wkElems : {n : N w} {n' : N w'} → ∣ n ∣ ≼ ∣ n' ∣ → ForAllW n (A ₀_) → ForAllW n' (A ₀_)
  wkElems is fam x = let (_ , x' , i) = is x in wk A i (fam x')

  wkCov : w ⊑ w' → CoverFam w → CoverFam w'
  wkCov i (n , f) = wkN i n , wkElems (wkN-ref i n) f

map𝒞' : {A B : USet} → (f : A →̇ B) → 𝒞' A →̇ 𝒞' B
map𝒞' f .apply (n , g) = n , f .apply ∘ g

𝒞'-distrib-×'-forth : {A B : USet} → 𝒞' (A ×' B) →̇ (𝒞' A ×' 𝒞' B)
𝒞'-distrib-×'-forth .apply (n , f) = (n , (proj₁ ∘ f)) , (n , (proj₂ ∘ f))

module _ {A B : USet} (run : {w : W} (n : N w) (f : ForAllW n (A ₀_)) → B ₀ w) where

  run𝒞' : 𝒞' A →̇ B
  run𝒞' .apply = uncurry run

module Nothing (ENF : EmptySeriality) where
  open EmptySeriality ENF

  empty' : {A : USet} → ⊤' →̇ 𝒞' A
  empty' .apply _ = emptyN[ _ ] , ⊥-elim ∘ emptyN-sub

  nothing' : {G A : USet} → G →̇ 𝒞' A
  nothing' {A = A} = empty' {A} ∘' unit'

-- (doesn't seem to have a name in Goldblatt10, but shows up nameless in Lemma 2.1)
module Strength (INF : Inclusion) where
  open Inclusion INF

  strength' : {A B : USet} → (A ×' 𝒞' B) →̇ 𝒞' (A ×' B)
  strength' {A} .apply {w} (a , n , bs) = n , (λ {v} v∈n → (wk A (N-ref n v∈n) a) , bs v∈n)

  swapped-strength' : {A B : USet} → (𝒞' A ×' B) →̇ 𝒞' (A ×' B)
  swapped-strength' {A} {B} = (map𝒞' (×'-swap {B} {A}) ∘' strength' {B} {A}) ∘' ×'-swap {𝒞' A} {B}

-- Inflationary (Goldblatt10)
module Return (WINF : WeakIdentity) where
  open WeakIdentity WINF

  point' : {A : USet} → A →̇ 𝒞' A
  point' {A} .apply {w} x = idN[ w ] , λ p → wk A (idN-ref p) x

  return' : {G A : USet} → G →̇ A → G →̇ 𝒞' A
  return' = point' ∘'_

  𝒞'-distrib-⊤'-back : ⊤' →̇ 𝒞' ⊤'
  𝒞'-distrib-⊤'-back = point'

-- Idempotent (Goldblatt10)
module Join (WTNF : WeakTransitivity) where
  open WeakTransitivity WTNF

  join' : {A : USet} → 𝒞' (𝒞' A) →̇ 𝒞' A
  join' {A} .apply {w} (n , h) = transN n (proj₁ ∘ h) , λ {v'} v∈jN →
    let (v , ((u , u∈n) , v∈h-) , v⊑v') = transN-ref n (proj₁ ∘ h) v∈jN
    in wk A v⊑v' (h u∈n .proj₂ v∈h-)

-- Multiplicative idempotent operator (Goldblatt10)
module StrongJoin (INF : Inclusion) (WTNF : WeakTransitivity) where
  open Strength INF public
  open Join WTNF public

  letin' : {G A B : USet} → (G →̇ 𝒞' A) → ((G ×' A) →̇ 𝒞' B) → (G →̇ 𝒞' B)
  letin' {G} {A} {B} t u = ((join' {B} ∘' map𝒞' u) ∘' strength' {G} {A}) ∘' ⟨ id' , t ⟩'

  𝒞'-distrib-×'-back : {A B : USet} → (𝒞' A ×' 𝒞' B) →̇ 𝒞' (A ×' B)
  𝒞'-distrib-×'-back {A} {B} = (join' {A ×' B} ∘' map𝒞' (swapped-strength' {A} {B})) ∘' strength' {𝒞' A} {B}

-- Closure operator (Goldblatt10)
module Monad (WINF : WeakIdentity) (WTNF : WeakTransitivity) where
  open Return WINF public
  open Join WTNF public

-- Nucleus (see Lemma 2.1 in Goldblatt10)
module StrongMonad (WCS : WeakCoverSystem NS) where

  open WeakCoverSystem WCS
  open Return identity public
  open StrongJoin inclusion transitivity public

-- Multiplicative (Goldblatt10)
module ×'-distr (WCNF : WeaklyClosedUnderInt) where
  open WeaklyClosedUnderInt WCNF

  𝒞'-distrib-×'-back : {A B : USet} → (𝒞' A ×' 𝒞' B) →̇ 𝒞' (A ×' B)
  𝒞'-distrib-×'-back {A} {B} .apply ((n1 , f1) , (n2 , f2)) = (n1 ⊗ n2) , λ p →
    let (f , g)        = ⊗-ref n1 n2
        (v1 , p1 , i1) = f p
        (v2 , p2 , i2) = g p
    in wk A i1 (f1 p1) , wk B i2 (f2 p2)

  𝒞'-pair : {G A B : USet} → G →̇ 𝒞' A → G →̇ 𝒞' B → G →̇ 𝒞' (A ×' B)
  𝒞'-pair {G} {A} {B} t u = 𝒞'-distrib-×'-back {A = A} {B = B} ∘' ⟨ t , u ⟩'

  letin' : {D G A B : USet} → (𝒞' D ×' G) →̇ 𝒞' A → (𝒞' (D ×' A) ×' G) →̇ B
    → (𝒞' D ×' G) →̇ B
  letin' {D} {G} {A} {B} t u = u ∘' ⟨ 𝒞'-pair {A = D} {B = A} proj₁' t , proj₂' ⟩'

module ⊤'-distr (SNF : Seriality) where
  open Seriality SNF

  𝒞'-distrib-⊤'-back : ⊤' →̇ 𝒞' ⊤'
  𝒞'-distrib-⊤'-back .apply _ = unitN[ _ ] , _

  unit𝒞' : {G : USet} → G →̇ 𝒞' ⊤'
  unit𝒞' = 𝒞'-distrib-⊤'-back ∘' unit'

  nec' : {G A : USet} → ⊤' →̇ A → G →̇ 𝒞' A
  nec' f = map𝒞' f ∘' unit𝒞'

module Extract (CINF : WeakCoIdentity) where

  open WeakCoIdentity CINF

  extract' : {A : USet} → 𝒞' A →̇ A
  extract' {A} .apply (n , h) = let (w , p , i) = N-ref n in wk A i (h p)

module Duplicate (WDNF : WeakDensity) where

  open WeakDensity WDNF

  duplicate' : {A : USet} → 𝒞' A →̇ 𝒞' (𝒞' A)
  duplicate' {A} .apply (n , h) = n , λ p → (denseN n p) , λ q → wk A (denseN-ref p q) (h p)

module CKBoxCover (CKBS : CKBoxModalSystem NS) where

  open CKBoxModalSystem CKBS

  open ×'-distr intclosed public
  open ⊤'-distr seriality public

module CS4BoxCover (CS4BS : CS4BoxModalSystem NS) where

  open CS4BoxModalSystem CS4BS

  open CKBoxCover ckBoxModalSytem public

  open Extract coidentity public
  open Duplicate density public
