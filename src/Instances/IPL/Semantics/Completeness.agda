open import Instances.IPL.System
open import Instances.IPL.Semantics.Lib
open import Instances.IPL.Semantics.Entailment
import Instances.IPL.Semantics.Interpretation as Interpretation

open import Data.Product
  using (Σ ; ∃ ; ∃₂ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)

open import Function
open import Data.Sum

module Instances.IPL.Semantics.Completeness where

data K : Ctx → Set where
  leaf    : (Γ : Ctx) → K Γ
  dead    : Γ ⊢ ⊥ → K Γ
  branch  : Γ ⊢ (a ∨ b) → K (Γ `, a) → K (Γ `, b) → K Γ

data _∈_ (Δ : Ctx) : K Γ → Set where
  here : Δ ∈ leaf Δ
  left : {n : Γ ⊢ (a ∨ b)} {k : K (Γ `, a)} {k' : K (Γ `, b)}
    → Δ ∈ k → Δ ∈ branch n k k'
  right : {n : Γ ⊢ (a ∨ b)} {k : K (Γ `, a)} {k' : K (Γ `, b)}
    → Δ ∈ k' → Δ ∈ branch n k k'

open import Frame.NFrame 𝕎 K _∈_

wkK : Γ ⊆ Γ' → K Γ → K Γ'
wkK i (leaf Δ)        = leaf _
wkK i (dead n)        = dead (wkTm i n)
wkK i (branch n k k') = branch (wkTm i n) (wkK (keep i) k) (wkK (keep i) k')

wkK-refines : (i : Γ ⊆ Γ') (k : K Γ) → k ≼ wkK i k
wkK-refines i (leaf _) here
  = _ , here , i
wkK-refines i (dead x) ()
wkK-refines i (branch x k1 k2) (left p)
  = let (Δ , p' , i') = wkK-refines (keep i) k1 p in
     (Δ , left p' , i')
wkK-refines i (branch x k1 k2) (right p)
  = let (Δ , p' , i') = wkK-refines (keep i) k2 p in
     (Δ , right p' , i')

reachable : (k : K Γ) → ForAllW k (Γ ⊆_)
reachable (leaf _)         here
  = ⊆-refl
reachable (dead x)         ()
reachable (branch x k1 k2) (left p)
  = freshWk ∙ reachable k1 p
reachable (branch x k1 k2) (right p)
  = freshWk ∙ reachable k2 p

transK : (k : K Γ) → ForAllW k K → K Γ
transK (leaf _)        f = f here
transK (dead x)        f = dead x
transK (branch x k k') f = branch x (transK k (f ∘ left)) (transK k' (f ∘ right))

transK-bwd-member : (k : K Γ) (h : ForAllW k K)
  → ForAllW (transK k h) (λ Δ → Exists∈ k (λ Γ∈k → Δ ∈ h Γ∈k))
transK-bwd-member (leaf Γ)        h p
  = Γ , here , p
transK-bwd-member (dead x)        h ()
transK-bwd-member (branch x k k') h (left p)  =
  let (vl , p' , pl) = transK-bwd-member k (h ∘ left) p
  in vl , left p' , pl
transK-bwd-member (branch x k k') h (right p) =
  let (vl , p' , pr) = transK-bwd-member k' (h ∘ right) p
  in vl , right p' , pr

Nuc : Nuclear
Nuc = record
  { refinement   = record
    { wkN         = wkK
    ; wkN-refines = wkK-refines
    }
  ; reachability = record
    { reachable = reachable }
  ; identity     = record
    { idN[_]         = leaf
    ; idN-bwd-member = λ { here → ≡-refl }
    }
  ; transitivity = record
    { transN            = transK
    ; transN-bwd-member = transK-bwd-member
    }
  }

open import USet.Base 𝕎
open import USet.Localized 𝕎 K _∈_ Nuc renaming
  (𝒞' to 𝒥'
  ; map𝒞' to map𝒥'
  ; run𝒞' to run𝒥'
  ; LUSetHA to ℛ) -- ℛ for "residualising model"

Tm' : Form → USet
Tm' a = uset (_⊢ a) wkTm

∨-I1' : Tm' a →̇ Tm' (a ∨ b)
∨-I1' .apply = ∨-I1

∨-I2' : Tm' b →̇ Tm' (a ∨ b)
∨-I2' .apply = ∨-I2

Tm₊ : Form → LUSet
Tm₊ a = luset (Tm' a) (run𝒥' {Tm' a} localizeTm)
  where
  localizeTm : (k : K Γ) → ForAllW k (_⊢ a) → Γ ⊢ a
  localizeTm (leaf _)         h = h here
  localizeTm (dead x)         h = ⊥-E x
  localizeTm (branch x k1 k2) h = ∨-E x (localizeTm k1 (h ∘ left)) (localizeTm k2 (h ∘ right))

open Interpretation ℛ (Tm₊ ∘ 𝕡) -- imports ⟦-⟧
open LUSet -- imports localize and 𝒳

--reify   : ∀ a → ⟦ a ⟧ →̇₊ (Tm₊ a)
-- or equivalently:
reify   : ∀ a → ⟦ a ⟧ .𝒳 →̇ Tm' a
reflect : ∀ a → Tm' a →̇ ⟦ a ⟧ .𝒳

reify (𝕡 i)   = id'
reify ⊤       = fun (λ _ → ⊤-I)
reify (a ⇒ b) = fun λ x → ⇒-I (reify b .apply (x freshWk (reflect a .apply (hyp zero))))
reify (a ∧ b) = fun λ x → ∧-I (reify a .apply (proj₁ x)) (reify b .apply (proj₂ x))
reify ⊥       = Tm₊ ⊥ .localize ∘' map𝒥' (⊥'-elim {Tm' ⊥})
reify (a ∨ b) = Tm₊ (a ∨ b) .localize ∘' map𝒥' [ ∨-I1' ∘' reify a  , ∨-I2' ∘' reify b ]'

reflect (𝕡 i)   = id'
reflect ⊤       = unit'
reflect (a ⇒ b) = fun λ n i x → reflect b .apply (⇒-E (wkTm i n) (reify a .apply x))
reflect (a ∧ b) = fun λ n → reflect a .apply (∧-E1 n) , reflect b .apply (∧-E2 n)
reflect ⊥       = fun λ n → dead n , λ{()}
reflect (a ∨ b) = fun λ n → branch n (leaf (_ `, a)) (leaf (_ `, b)) ,
  λ { (left here)  → inj₁ (reflect a .apply (hyp zero))
    ; (right here) → inj₂ (reflect b .apply (hyp zero))
    }

idEnv : ∀ Γ → ⟦ Γ ⟧c .𝒳 ₀ Γ
idEnv []       = _
idEnv (Γ `, a) = wk (⟦ Γ ⟧c .𝒳) freshWk (idEnv Γ) , reflect a .apply (hyp zero)

quot : (⟦ Γ ⟧c →̇₊ ⟦ a ⟧) → Γ ⊢ a
quot {Γ} {a} f = reify a .apply (f .apply (idEnv Γ))

completeness : Γ ⊨ a → Γ ⊢ a
completeness f = quot (f ℛ (Tm₊ ∘ 𝕡))
