{-# OPTIONS --safe --without-K #-}
module Context.Properties (Ty : Set) where

open import Data.Product
  using (Σ ; ∃ ; ∃₂ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; module ≡-Reasoning)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)

open import Context.Base Ty

open import Frame.IFrame

open import Function

private
  variable
    a b c d : Ty

𝕎 : Preorder Ctx _⊑_
𝕎 = record { ⊑-trans = ⊑-trans ; ⊑-refl = ⊑-refl }

⊑-trans-unit-left : (w : Γ' ⊑ Γ) → ⊑-refl ∙ w ≡ w
⊑-trans-unit-left base      = ≡-refl
⊑-trans-unit-left (drop w)  = cong drop (⊑-trans-unit-left w)
⊑-trans-unit-left (keep w)  = cong keep (⊑-trans-unit-left w)

-- weakening composition obeys the right identity law
⊑-trans-unit-right : (w : Γ' ⊑ Γ) → w ∙ ⊑-refl ≡ w
⊑-trans-unit-right base      = ≡-refl
⊑-trans-unit-right (drop w)  = cong drop (⊑-trans-unit-right w)
⊑-trans-unit-right (keep w)  = cong keep (⊑-trans-unit-right w)

-- weakening composition is associative
⊑-trans-assoc : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (w3 : Γ4 ⊑ Γ3) (w2 : Γ3 ⊑ Γ2) → (w1 : Γ2 ⊑ Γ1)
  → (w3 ∙ w2) ∙ w1 ≡ w3 ∙ (w2 ∙ w1)
⊑-trans-assoc w3         w2         base       = ≡-refl
⊑-trans-assoc w3         w2         (drop w1)  = cong drop (⊑-trans-assoc w3 w2 w1)
⊑-trans-assoc w3         (drop w2)  (keep w1)  = cong drop (⊑-trans-assoc w3 w2 w1)
⊑-trans-assoc (drop w3)  (keep w2)  (keep w1)  = cong drop (⊑-trans-assoc w3 w2 w1)
⊑-trans-assoc (keep w3)  (keep w2)  (keep w1)  = cong keep (⊑-trans-assoc w3 w2 w1)

𝒲 : IFrame Ctx _⊑_
𝒲 = record
      { ⊑-trans           = _∙_
      ; ⊑-trans-assoc     = ⊑-trans-assoc
      ; ⊑-refl            = ⊑-refl
      ; ⊑-trans-unit-left = ⊑-trans-unit-left
      ; ⊑-trans-unit-right  = ⊑-trans-unit-right
      }

wkVar-pres-⊑-refl : (x : Var Γ a) → wkVar ⊑-refl x ≡ x
wkVar-pres-⊑-refl v0       = ≡-refl
wkVar-pres-⊑-refl (succ x) = cong succ (wkVar-pres-⊑-refl x)

wkVar-pres-⊑-trans : (w : Γ ⊑ Γ') (w' : Γ' ⊑ Δ) (x : Var Γ a)
  → wkVar (w ∙ w') x ≡ wkVar w' (wkVar w x)
wkVar-pres-⊑-trans (drop w) (drop w') zero     = cong succ (wkVar-pres-⊑-trans (drop w) w' zero)
wkVar-pres-⊑-trans (drop w) (keep w') zero     = cong succ (wkVar-pres-⊑-trans w w' zero)
wkVar-pres-⊑-trans (keep w) (drop w') zero     = cong succ (wkVar-pres-⊑-trans (keep w) w' zero)
wkVar-pres-⊑-trans (keep w) (keep w') zero     = ≡-refl
wkVar-pres-⊑-trans (drop w) (drop w') (succ x) = cong succ (wkVar-pres-⊑-trans (drop w) w' (succ x))
wkVar-pres-⊑-trans (drop w) (keep w') (succ x) = cong succ (wkVar-pres-⊑-trans w w' (succ x))
wkVar-pres-⊑-trans (keep w) (drop w') (succ x) = cong succ (wkVar-pres-⊑-trans (keep w) w' (succ x))
wkVar-pres-⊑-trans (keep w) (keep w') (succ x) = cong succ (wkVar-pres-⊑-trans w w' x)

freshWk-natural : (w : Γ ⊑ Γ') → w ∙ freshWk[ Γ' , a ] ≡ freshWk[ Γ , a ] ∙ keep w
freshWk-natural w = cong drop (≡-trans (⊑-trans-unit-right w) (≡-sym (⊑-trans-unit-left w)))

-- weakening a variable index increments
wkIncr : (x : Var Γ a) → wkVar freshWk[ Γ , b ] x ≡ succ x
wkIncr zero     = ≡-refl
wkIncr (succ x) = cong succ (cong succ (wkVar-pres-⊑-refl x))

module IPLBaseSystem (⊥ : Ty) (_∨_ : Ty → Ty → Ty) (_⊢_ : Ctx → Ty → Set)
  (wkTm : {a : Ty} {Γ Γ' : Ctx} → Γ ⊑ Γ' → Γ ⊢ a → Γ' ⊢ a) where

  data K₊ : Ctx → Set where
    leaf    : (Γ : Ctx) → K₊ Γ
    dead    : Γ ⊢ ⊥ → K₊ Γ
    branch  : Γ ⊢ (a ∨ b) → K₊ (Γ `, a) → K₊ (Γ `, b) → K₊ Γ

  data _∈₊_ (Δ : Ctx) : K₊ Γ → Set where
    here : Δ ∈₊ leaf Δ
    left : {n : Γ ⊢ (a ∨ b)} {k : K₊ (Γ `, a)} {k' : K₊ (Γ `, b)}
      → Δ ∈₊ k → Δ ∈₊ branch n k k'
    right : {n : Γ ⊢ (a ∨ b)} {k : K₊ (Γ `, a)} {k' : K₊ (Γ `, b)}
      → Δ ∈₊ k' → Δ ∈₊ branch n k k'
  
  open import Neighborhood.Lib 𝕎 K₊ _∈₊_
    renaming (∣_∣ to ∣_∣₊ ; ForAllW to ForAllW₊) public
             
  open import Neighborhood.Systems 𝕎

  wkK₊ : Γ ⊑ Γ' → K₊ Γ → K₊ Γ'
  wkK₊ i (leaf Δ)        = leaf _
  wkK₊ i (dead n)        = dead (wkTm i n)
  wkK₊ i (branch n k k') = branch (wkTm i n) (wkK₊ (keep i) k) (wkK₊ (keep i) k')

  wkK₊-ref : (i : Γ ⊑ Γ') (k : K₊ Γ) → ∣ k ∣₊ ≼ ∣ wkK₊ i k ∣₊
  wkK₊-ref i (leaf _) here
    = _ , here , i
  wkK₊-ref i (dead x) ()
  wkK₊-ref i (branch x k1 k2) (left p)
    = let (Δ , p' , i') = wkK₊-ref (keep i) k1 p in
       (Δ , left p' , i')
  wkK₊-ref i (branch x k1 k2) (right p)
    = let (Δ , p' , i') = wkK₊-ref (keep i) k2 p in
       (Δ , right p' , i')

  K₊-ref : (k : K₊ Γ) → ∣ k ∣₊ ⊆ (↑ Γ)
  K₊-ref (leaf _)         here
    = ⊑-refl
  K₊-ref (dead x)         ()
  K₊-ref (branch x k1 k2) (left p)
    = freshWk ∙ K₊-ref k1 p
  K₊-ref (branch x k1 k2) (right p)
    = freshWk ∙ K₊-ref k2 p

  idK₊ = leaf

  idK₊-sub : ∣ idK₊ Γ ∣₊ ⊆ ⟨ Γ ⟩
  idK₊-sub here = ≡-refl

  transK₊ : (k : K₊ Γ) → ForAllW₊ k K₊ → K₊ Γ
  transK₊ (leaf _)        f = f here
  transK₊ (dead x)        f = dead x
  transK₊ (branch x k k') f = branch x (transK₊ k (f ∘ left)) (transK₊ k' (f ∘ right))

  transK₊-sub : (k : K₊ Γ) (h : ForAllW₊ k K₊)
    → ∣ transK₊ k h ∣₊ ⊆ ⨆ ∣ k ∣₊ (∣_∣₊ ∘ h)
  transK₊-sub (leaf Γ)        h p
    = (Γ , here) , p
  transK₊-sub (dead x)        h ()
  transK₊-sub (branch x k k') h (left p)  =
    let (vl , p') , pl = transK₊-sub k (h ∘ left) p
    in (vl , left p') , pl
  transK₊-sub (branch x k k') h (right p) =
    let (vl , p') , pr = transK₊-sub k' (h ∘ right) p
    in (vl , right p') , pr
  
  NS₊ : NeighborhoodSystem
  NS₊ = record
    { N          = K₊
    ; _∈_        = _∈₊_
    ; refinement = record { wkN = wkK₊ ; wkN-ref = wkK₊-ref }
    }

  CS₊ : CoverSystem NS₊
  CS₊ = record
    { inclusion    = record { N-ref = K₊-ref }
    ; identity     = record { idN[_] = idK₊ ; idN-sub = idK₊-sub }
    ; transitivity = record { transN = transK₊ ; transN-sub = transK₊-sub }
    }

  WCS₊ : WeakCoverSystem NS₊
  WCS₊ = CoverSystem.weakCoverSystem CS₊

  open import USet.Base 𝕎 public
  open import USet.Localized 𝕎 WCS₊ public -- ℛ for "residualising model"

  -- Observations that are not used in the construction of the system
  -- but allow us to get an understanding of exhibited properties 
  module Observations where

    transK₊-sub⁻¹ : (k : K₊ Γ) (h : ForAllW₊ k K₊)
      → ⨆ ∣ k ∣₊ (∣_∣₊ ∘ h) ⊆ ∣ transK₊ k h ∣₊
    transK₊-sub⁻¹ (leaf Γ)        h ((.Γ , here) , p)
      = p
    transK₊-sub⁻¹ (branch x k k') h ((_ , left p) , q)
      = left (transK₊-sub⁻¹ k (h ∘ left) ((-, p) , q))
    transK₊-sub⁻¹ (branch x k k') h ((_ , right p) , q)
      = right (transK₊-sub⁻¹ k' (h ∘ right) ((-, p) , q))

    transK₊-equ : (k : K₊ Γ) (h : ForAllW₊ k K₊)
      → ∣ transK₊ k h ∣₊ ≐ ⨆ ∣ k ∣₊ (∣_∣₊ ∘ h)
    transK₊-equ k h = transK₊-sub k h , transK₊-sub⁻¹ k h

    idK₊-sub⁻¹ : ⟨ Γ ⟩ ⊆ ∣ idK₊ Γ ∣₊
    idK₊-sub⁻¹ ≡-refl = here

    idK₊-equ : ∣ idK₊ Γ ∣₊ ≐ ⟨ Γ ⟩
    idK₊-equ = idK₊-sub , idK₊-sub⁻¹

    hyperTransitivity : HyperTransitivity
    hyperTransitivity = record
      { transN     = transK₊
      ; transN-equ = transK₊-equ
      }

    hyperIdentity : HyperIdentity
    hyperIdentity = record
      { idN[_]  = idK₊
      ; idN-equ = idK₊-equ
      }
    
