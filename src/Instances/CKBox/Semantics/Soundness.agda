open import HeytingAlgebras
open import Instances.CKBox.System
open import Instances.CKBox.Semantics.Entailment
import Instances.CKBox.Semantics.Interpretation as Interpretation
open import Data.Product using (_×_ ; _,_)

module Instances.CKBox.Semantics.Soundness where

module Proof
  (𝒜 : CKBoxAlgebra)
  (open CKBoxAlgebra 𝒜 using (Carrier))
  (V𝕡 : Atom → Carrier)
  where

  open Interpretation 𝒜 V𝕡

  open CKBoxAlgebra 𝒜
    using (ℋ)
    renaming ( maximum to unit'
             ; minimum to init'
             ; refl to ≤-refl
             ; trans to ≤-trans
             ; ∧-greatest to ⟨_,_⟩'
             ; x∧y≤x to proj₁'
             ; x∧y≤y to proj₂'
             ; transpose-⇨ to curry'
             ; transpose-∧ to uncurry'
             ; x≤x∨y to inj₁'
             ; y≤x∨y to inj₂'
             ; ∨-least to [_,_]'
             ; ◻-distrib-⊤-back to ◻'-distrib-⊤'-back
             ; ◻-monotone to ◻'-map
             ; ◻-distrib-∧-back to ◻'-distrib-∧'-back
             ) public

  open import Relation.Binary.Lattice.Properties.HeytingAlgebra ℋ
    renaming (∧-distribˡ-∨-≤ to ∧'-distr-∨'-forth) public

  open HeytingAlgebraProperties ℋ using (∧-assoc-forth)

  -- Interpretation is sound for hypothesis
  ⟦-⟧-sound-hyp : Var Γ a → ⟦ Γ ⟧c ≤ ⟦ a ⟧
  ⟦-⟧-sound-hyp {Γ `, a} {.a} zero
    = proj₂' ⟦ Γ ⟧c ⟦ a ⟧
  ⟦-⟧-sound-hyp {Γ `, b} {a} (succ x)
    = ≤-trans (proj₁' ⟦ Γ ⟧c ⟦ b ⟧) (⟦-⟧-sound-hyp x)

  -- Interpretation is sound for derivations
  ⟦-⟧-sound : Δ ⨾ Γ ⊢ a → ⟦ Δ , Γ ⟧c₂ ≤ ⟦ a ⟧
  ⟦-⟧-sound {Δ} {Γ} {a} (hyp x)
    = ≤-trans (proj₂' (◻' ⟦ Δ ⟧c) ⟦ Γ ⟧c) (⟦-⟧-sound-hyp x)
  ⟦-⟧-sound {Δ} {Γ} {_} ⊤-I
    = unit' ⟦ Δ , Γ ⟧c₂
  ⟦-⟧-sound {_} {_} {a} (⊥-E t)
    = ≤-trans (⟦-⟧-sound t) (init' ⟦ a ⟧)
  ⟦-⟧-sound {Δ} {Γ} {_} (⇒-I {a} t)
    = curry' (≤-trans (∧-assoc-forth (◻' ⟦ Δ ⟧c) ⟦ Γ ⟧c ⟦ a ⟧) (⟦-⟧-sound t))
  ⟦-⟧-sound (⇒-E t u)
    = ≤-trans ⟨ ≤-refl , ⟦-⟧-sound u ⟩' (uncurry' (⟦-⟧-sound t))
  ⟦-⟧-sound (∧-I t u)
    = ⟨ ⟦-⟧-sound t , ⟦-⟧-sound u ⟩'
  ⟦-⟧-sound {Δ} {Γ} {a} (∧-E1 {.a} {b} t)
    = ≤-trans (⟦-⟧-sound t) (proj₁' ⟦ a ⟧ ⟦ b ⟧)
  ⟦-⟧-sound {Δ} {Γ} {b} (∧-E2 {a} {.b} t)
    = ≤-trans (⟦-⟧-sound t) (proj₂' ⟦ a ⟧ ⟦ b ⟧)
  ⟦-⟧-sound {Δ} {Γ} {_} (∨-I1 {a} {b} t)
    = ≤-trans (⟦-⟧-sound t) (inj₁' ⟦ a ⟧ ⟦ b ⟧)
  ⟦-⟧-sound {Δ} {Γ} {_} (∨-I2 {a} {b} t)
    = ≤-trans (⟦-⟧-sound t) (inj₂' ⟦ b ⟧ ⟦ a ⟧)
  ⟦-⟧-sound {Δ} {Γ} {c} (∨-E {a} {b} {.c} t u1 u2)
    = ≤-trans ⟨ ≤-refl , ⟦-⟧-sound t ⟩'
        (≤-trans (∧'-distr-∨'-forth  ⟦ Δ , Γ ⟧c₂ ⟦ a ⟧ ⟦ b ⟧)
          [ ≤-trans (∧-assoc-forth (◻' ⟦ Δ ⟧c) ⟦ Γ ⟧c ⟦ a ⟧) (⟦-⟧-sound u1)
          , ≤-trans (∧-assoc-forth (◻' ⟦ Δ ⟧c) ⟦ Γ ⟧c ⟦ b ⟧) (⟦-⟧-sound u2)
          ]')
  ⟦-⟧-sound {Δ} {Γ} {c} (◻-I {a} t)
    = ≤-trans
        (proj₁' (◻' ⟦ Δ ⟧c) ⟦ Γ ⟧c)
        (◻'-map (≤-trans
          ⟨ ≤-trans (unit' ⟦ Δ ⟧c) ◻'-distrib-⊤'-back , ≤-refl ⟩'
          (⟦-⟧-sound t)))
  ⟦-⟧-sound {Δ} {Γ} {c} (◻-E t u)
    = ≤-trans
        ⟨ ≤-trans ⟨ proj₁' (◻' ⟦ Δ ⟧c) ⟦ Γ ⟧c , ⟦-⟧-sound t ⟩' ◻'-distrib-∧'-back
        , proj₂' (◻' ⟦ Δ ⟧c) ⟦ Γ ⟧c ⟩'
        (⟦-⟧-sound u)

-- deductive soundness
soundness : Δ ⨾ Γ ⊢ a → Δ ⨾ Γ ⊨ a
soundness t 𝒜 V𝕓 = let open Proof 𝒜 V𝕓 in ⟦-⟧-sound t
