{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.Semantics.Soundness where

open import NonDistributiveAlgebras

open import Instances.LatLog.System
open import Instances.LatLog.Semantics.Entailment
import Instances.LatLog.Semantics.Interpretation as Interpretation

module Proof
  (ℒ : BoundedLattice)
  (open BoundedLattice ℒ using (Carrier))
  (V𝕡 : Atom → Carrier) -- Valuation of proposition 𝕡
  where

  open Interpretation ℒ V𝕡
  
  open BoundedLattice ℒ
    using ()
    renaming ( maximum to unit'
             ; minimum to init'
             ; refl to ≤-refl
             ; trans to ≤-trans
             ; ∧-greatest to ⟨_,_⟩'
             ; x∧y≤x to proj₁'
             ; x∧y≤y to proj₂'
             ; x≤x∨y to inj₁'
             ; y≤x∨y to inj₂'
             ; ∨-least to [_,_]'
             ) public
  open import Relation.Binary.Lattice.Properties.BoundedLattice ℒ public

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
  ⟦-⟧-sound {Γ} {_} (∨-I1 {.Γ} {a} {b} t)
    = ≤-trans (⟦-⟧-sound t) (inj₁' ⟦ a ⟧ ⟦ b ⟧)
  ⟦-⟧-sound {Γ} {_} (∨-I2 {.Γ} {a} {b} t)
    = ≤-trans (⟦-⟧-sound t) (inj₂' ⟦ b ⟧ ⟦ a ⟧)
  ⟦-⟧-sound {Γ} {c} (∨-E {.Γ} {a} {b} {.c} t u1 u2)
    = ≤-trans ⟨ ≤-refl , ⟦-⟧-sound t ⟩'
        (≤-trans (proj₂' ⟦ Γ ⟧c ⟦ a ∨ b ⟧)
          [ ≤-trans ⟨ unit' ⟦ a ⟧ , ≤-refl ⟩' (⟦-⟧-sound u1)
          , ≤-trans ⟨ unit' ⟦ b ⟧ , ≤-refl ⟩' (⟦-⟧-sound u2) ]')

-- algebraic soundness
soundness : Γ ⊢ a → Γ ⊨ₐ a
soundness t 𝒫 V𝕓 = let open Proof 𝒫 V𝕓 in ⟦-⟧-sound t
