{-# OPTIONS --safe --without-K #-}

module Instances.MPL.Semantics.Soundness where

open import NonDistributiveAlgebras

open import Instances.MPL.System
open import Instances.MPL.Semantics.Entailment
import Instances.MPL.Semantics.Interpretation as Interpretation

module Proof
  (𝒫 : MPLAlgebra)
  (open MPLAlgebra 𝒫 using (Carrier))
  (V𝕡 : Atom → Carrier) -- Valuation of proposition 𝕡
  where

  open Interpretation 𝒫 V𝕡
  
  open MPLAlgebra 𝒫
    using ()
    renaming ( maximum to unit'
             ; minimum to init'
             ; refl to ≤-refl
             ; trans to ≤-trans
             ; ∧-greatest to ⟨_,_⟩'
             ; x∧y≤x to proj₁'
             ; x∧y≤y to proj₂'
             ; ∨-least to [_,_]'
             ) public
--  open import Relation.Binary.Lattice.Properties.MPLAlgebra 𝒫 public

  -- Interpretation is sound for hypothesis
  ⟦-⟧-sound-hyp : Var Γ a → ⟦ Γ ⟧c ≤ ⟦ a ⟧
  ⟦-⟧-sound-hyp {Γ `, a} {.a} zero
    = proj₂' ⟦ Γ ⟧c ⟦ a ⟧
  ⟦-⟧-sound-hyp {Γ `, b} {a} (succ x)
    = ≤-trans (proj₁' ⟦ Γ ⟧c ⟦ b ⟧) (⟦-⟧-sound-hyp x)

  -- Interpretation is sound for derivations
  ⟦-⟧-sound : Γ ⊢ a → ⟦ Γ ⟧c ≤ ⟦ a ⟧
  ⟦-⟧-sound {_} {a} (hyp x)
    = ⟦-⟧-sound-hyp x
  ⟦-⟧-sound {Γ} {_} ⊤-I
    = unit' ⟦ Γ ⟧c
  ⟦-⟧-sound {_} {a} (⊥-E t)
    = ≤-trans (⟦-⟧-sound t) (init' ⟦ a ⟧)
  ⟦-⟧-sound (∧-I t u)
    = ⟨ ⟦-⟧-sound t , ⟦-⟧-sound u ⟩'
  ⟦-⟧-sound {Γ} {a} (∧-E1 {.Γ} {.a} {b} t)
    = ≤-trans (⟦-⟧-sound t) (proj₁' ⟦ a ⟧ ⟦ b ⟧)
  ⟦-⟧-sound {Γ} {b} (∧-E2 {.Γ} {a} {.b} t)
    = ≤-trans (⟦-⟧-sound t) (proj₂' ⟦ a ⟧ ⟦ b ⟧)
  ⟦-⟧-sound {Γ} {c} (∨-Cm t)
    = ≤-trans (⟦-⟧-sound t) ∨-comm
  ⟦-⟧-sound {Γ} {c} (∨-Id t)
    = ≤-trans (⟦-⟧-sound t) ∨-idem
  ⟦-⟧-sound {Γ} {c} (∨-Wk t)
    = ≤-trans (⟦-⟧-sound t) ∨-weak
  ⟦-⟧-sound {Γ} {c} (∨-M {a = a} {b} t t₁ t₂)
    = ≤-trans (⟦-⟧-sound t) (∨-mon
      (≤-trans ⟨ unit' ⟦ a ⟧ , ≤-refl ⟩' (⟦-⟧-sound t₁))
      (≤-trans ⟨ unit' ⟦ b ⟧ , ≤-refl ⟩' (⟦-⟧-sound t₂)))

-- algebraic soundness
soundness : Γ ⊢ a → Γ ⊨ₐ a
soundness t 𝒫 V𝕓 = let open Proof 𝒫 V𝕓 in ⟦-⟧-sound t

