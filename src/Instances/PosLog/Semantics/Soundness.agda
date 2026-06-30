{-# OPTIONS --safe --without-K #-}

module Instances.PosLog.Semantics.Soundness where

open import NonDistributiveAlgebras

open import Instances.PosLog.System
open import Instances.PosLog.Semantics.Entailment
import Instances.PosLog.Semantics.Interpretation as Interpretation

module Proof
  (𝒜 : PosLogAlgebra)
  (open PosLogAlgebra 𝒜 using (Carrier))
  (V𝕡 : Atom → Carrier) -- Valuation of proposition 𝕡
  where

  open Interpretation 𝒜 V𝕡
  
  open PosLogAlgebra 𝒜
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
    = ≤-trans (⟦-⟧-sound t) ∨-idemˡ
  ⟦-⟧-sound {Γ} {c} (∨-Wk t)
    = ≤-trans (⟦-⟧-sound t) ∨-wken₂
  ⟦-⟧-sound {Γ} {c} (∨-M {a = a} {b} t t₁ t₂)
    = ≤-trans (⟦-⟧-sound t) (∨-mon
      (≤-trans ⟨ unit' ⟦ a ⟧ , ≤-refl ⟩' (⟦-⟧-sound t₁))
      (≤-trans ⟨ unit' ⟦ b ⟧ , ≤-refl ⟩' (⟦-⟧-sound t₂)))

-- algebraic soundness
soundness : Γ ⊢ a → Γ ⊨ₐ a
soundness t 𝒜 V𝕓 = let open Proof 𝒜 V𝕓 in ⟦-⟧-sound t

