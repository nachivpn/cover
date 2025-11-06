{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame
import Frame.NFrame as NF

module USet.Cover
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (𝕎   : Preorder W _⊆_)
  (N   : W → Set)
  (_∈_ : (v : W) {w : W} → N w → Set)
  (let open NF 𝕎 N _∈_)
  (MNF  : Refinement) -- MNF for "Monotonic Neighborhood Frame"
  (let open Refinement MNF)
  where

open import Function using (id ; const ; _∘_)

--open import Data.Unit
open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; uncurry)
open import Data.Empty
--open import Data.Sum

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

  wkElems : {n : N w} {n' : N w'} → n ≼ n' → ForAllW n (A ₀_) → ForAllW n' (A ₀_)
  wkElems is fam x = let (_ , x' , i) = is x in wk A i (fam x')

  wkCov : w ⊆ w' → CoverFam w → CoverFam w'
  wkCov i (n , f) = wkN i n , wkElems (wkN-refines i n) f

map𝒞' : {A B : USet} → (f : A →̇ B) → 𝒞' A →̇ 𝒞' B
map𝒞' f .apply (n , g) = n , f .apply ∘ g

×'-distr-forth' : {A B : USet} → 𝒞' (A ×' B) →̇ (𝒞' A ×' 𝒞' B)
×'-distr-forth' .apply (n , f) = (n , (proj₁ ∘ f)) , (n , (proj₂ ∘ f))

module _ {A B : USet} (run : {w : W} (n : N w) (f : ForAllW n (A ₀_)) → B ₀ w) where

  run𝒞' : 𝒞' A →̇ B
  run𝒞' .apply = uncurry run

module Nothing (ENF : Empty) where
  open Empty ENF

  empty' : {A : USet} → ⊤' →̇ 𝒞' A
  empty' .apply _ = emptyN[ _ ] , ⊥-elim ∘ emptyN-bwd-absurd

  nothing' : {G A : USet} → G →̇ 𝒞' A
  nothing' {A = A} = empty' {A} ∘' unit'

-- (doesn't seem to have a name in Goldblatt10, but shows up nameless in Lemma 2.1)
module Strength (RNF : Reachability) where
  open Reachability RNF

  strength' : {A B : USet} → (A ×' 𝒞' B) →̇ 𝒞' (A ×' B)
  strength' {A} .apply {w} (a , n , bs) = n , (λ {v} v∈n → (wk A (reachable n v∈n) a) , bs v∈n)

  swapped-strength' : {A B : USet} → (𝒞' A ×' B) →̇ 𝒞' (A ×' B)
  swapped-strength' {A} {B} = (map𝒞' (×'-swap {B} {A}) ∘' strength' {B} {A}) ∘' ×'-swap {𝒞' A} {B}

-- Inflationary (Goldblatt10)
module Return (WINF : WeakIdentity) where
  open WeakIdentity WINF

  point' : {A : USet} → A →̇ 𝒞' A
  point' {A} .apply {w} x = idN[ w ] , λ p → wk A (idN-bwd-reachable p) x

  return' : {G A : USet} → G →̇ A → G →̇ 𝒞' A
  return' = point' ∘'_

-- Idempotent (Goldblatt10)
module Join (WTNF : WeakTransitivity) where
  open WeakTransitivity WTNF

  join' : {A : USet} → 𝒞' (𝒞' A) →̇ 𝒞' A
  join' {A} .apply {w} (n , h) = transN n (proj₁ ∘ h) , λ {v'} v∈jN →
    let u , u∈n , v , v∈h- , v⊆v' = transN-bwd-reachable n (proj₁ ∘ h) v∈jN
    in wk A v⊆v' (h u∈n .proj₂ v∈h-)

-- Multiplicative idempotent operator (Goldblatt10)
module StrongJoin (RNF : Reachability) (WTNF : WeakTransitivity) where
  open Strength RNF public
  open Join WTNF public

  letin' : {G A B : USet} → (G →̇ 𝒞' A) → ((G ×' A) →̇ 𝒞' B) → (G →̇ 𝒞' B)
  letin' {G} {A} {B} t u = ((join' {B} ∘' map𝒞' u) ∘' strength' {G} {A}) ∘' ⟨ id' , t ⟩'

  ×'-distr-back' : {A B : USet} → (𝒞' A ×' 𝒞' B) →̇ 𝒞' (A ×' B)
  ×'-distr-back' {A} {B} = (join' {A ×' B} ∘' map𝒞' (swapped-strength' {A} {B})) ∘' strength' {𝒞' A} {B}

-- Closure operator (Goldblatt10)
module Monad (WINF : WeakIdentity) (WTNF : WeakTransitivity) where
  open Return WINF public
  open Join WTNF public

-- Nucleus (see Lemma 2.1 in Goldblatt10)
module StrongMonad (RNF : Reachability) (WINF : WeakIdentity) (WTNF : WeakTransitivity) where
  open Return WINF public
  open StrongJoin RNF WTNF public

-- Multiplicative (Goldblatt10)
module ×'-distr (WCNF : WeaklyClosedUnderInt) where
  open WeaklyClosedUnderInt WCNF

  ×'-distr-back' : {A B : USet} → (𝒞' A ×' 𝒞' B) →̇ 𝒞' (A ×' B)
  ×'-distr-back' {A} {B} .apply ((n1 , f1) , (n2 , f2)) = (n1 ⊗ n2) , λ p →
    let (v1 , v2 , p1 , i1 , p2 , i2) = ⊗-bwd-reachable n1 n2 p
    in wk A i1 (f1 p1) , wk B i2 (f2 p2)

  pr𝒞' : {G A B : USet} → G →̇ 𝒞' A → G →̇ 𝒞' B → G →̇ 𝒞' (A ×' B)
  pr𝒞' {G} {A} {B} t u = ×'-distr-back' {A = A} {B = B} ∘' ⟨ t , u ⟩'

  letin' : {D G A B : USet} → (𝒞' D ×' G) →̇ 𝒞' A → (𝒞' (D ×' A) ×' G) →̇ B
    → (𝒞' D ×' G) →̇ B
  letin' {D} {G} {A} {B} t u = u ∘' ⟨ pr𝒞' {A = D} {B = A} proj₁' t , proj₂' ⟩'

module ⊤'-distr (NENF : NonEmpty) where
  open NonEmpty NENF

  ⊤'-distr-back' : ⊤' →̇ 𝒞' ⊤'
  ⊤'-distr-back' .apply _ = unitN[ _ ] , _

  unit𝒞' : {G : USet} → G →̇ 𝒞' ⊤'
  unit𝒞' = ⊤'-distr-back' ∘' unit'

  nec' : {G A : USet} → ⊤' →̇ A → G →̇ 𝒞' A
  nec' f = map𝒞' f ∘' unit𝒞'
