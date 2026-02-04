open import HeytingAlgebras
open import Instances.PLL.System
open import Instances.PLL.Semantics.Entailment
import Instances.PLL.Semantics.Interpretation as Interpretation

module Instances.PLL.Semantics.Soundness where

module Proof
  (𝒜 : PLLAlgebra)
  (open PLLAlgebra 𝒜 using (Carrier))
  (V𝕡 : Atom → Carrier) -- Valuation of proposition 𝕡
  where

  open Interpretation 𝒜 V𝕡

  open PLLAlgebra 𝒜
    using ()
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
             ; x≤◇x to point'
             ; ◇◇x≤◇x to join'
             ; x∧◇y≤◇⟨x∧y⟩ to strong'
             ; ◇-monotone to fmap'
             ) public
  
  open import Relation.Binary.Lattice.Properties.HeytingAlgebra ℋ
    renaming (∧-distribˡ-∨-≤ to ∧'-distr-∨'-forth) public

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
  ⟦-⟧-sound (⇒-I t)
    = curry' (⟦-⟧-sound t)
  ⟦-⟧-sound (⇒-E t u)
    = ≤-trans ⟨ ≤-refl , ⟦-⟧-sound u ⟩' (uncurry' (⟦-⟧-sound t))
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
        (≤-trans (∧'-distr-∨'-forth ⟦ Γ ⟧c ⟦ a ⟧ ⟦ b ⟧) [ ⟦-⟧-sound u1 , ⟦-⟧-sound u2 ]')
  ⟦-⟧-sound {Γ} {c} (◇-I t)
    = ≤-trans (⟦-⟧-sound t) point'
  ⟦-⟧-sound {Γ} {c} (◇-B t u)
    = ≤-trans ⟨ ≤-refl , ⟦-⟧-sound t ⟩' (≤-trans strong' (≤-trans (fmap' (⟦-⟧-sound u)) join'))

-- deductive soundness
soundness : Γ ⊢ a → Γ ⊨ a
soundness t 𝒜 V𝕓 = let open Proof 𝒜 V𝕓 in ⟦-⟧-sound t
