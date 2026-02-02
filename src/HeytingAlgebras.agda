{-# OPTIONS --safe --without-K #-}

open import Level using (0ℓ ; suc)
open import Relation.Binary.Lattice.Bundles renaming (HeytingAlgebra to LHeytingAlgebra)

module HeytingAlgebras where

private 1ℓ = suc 0ℓ
HeytingAlgebra = LHeytingAlgebra 1ℓ 0ℓ 0ℓ
module HeytingAlgebra = LHeytingAlgebra

record MonAlgebra : Set₂ where
  field
    heytingAlgebra : HeytingAlgebra

  open HeytingAlgebra heytingAlgebra public

  field
    ○_         : Carrier → Carrier
    ○-resp-≈   : {x y : Carrier} → x ≈ y → ○ x ≈ ○ y
    ○-monotone : {x y : Carrier} → x ≤ y → ○ x ≤ ○ y

  ○-distrib-∧-forth : {x y : Carrier} → ○ (x ∧ y) ≤ ○ x ∧ ○ y
  ○-distrib-∧-forth = ∧-greatest (○-monotone (x∧y≤x _ _)) (○-monotone (x∧y≤y _ _))

  ○-distrib-⊤-forth : ○ ⊤ ≤ ⊤
  ○-distrib-⊤-forth = maximum (○ ⊤)

  ○-distrib-∨-back : {x y : Carrier} → ○ x ∨ ○ y ≤ ○ (x ∨ y)
  ○-distrib-∨-back = ∨-least (○-monotone (x≤x∨y _ _)) (○-monotone (y≤x∨y _ _))
  
record CKBoxAlgebra : Set₂ where

  field
    heytingAlgebra : HeytingAlgebra

  open HeytingAlgebra heytingAlgebra public

  field
    -- operator
    ◻_          : Carrier → Carrier
    ◻-resp-≈    : {x y : Carrier} → x ≈ y → ◻ x ≈ ◻ y

    -- structure
    ◻-distrib-∧      : {x y : Carrier} → ◻ (x ∧ y) ≈ ◻ x ∧ ◻ y
    ◻-distrib-⊤-back : ⊤ ≤ ◻ ⊤

  ◻-monotone : {a b : Carrier} → a ≤ b → ◻ a ≤ ◻ b
  ◻-monotone {a} {b} i = trans ◻a≤◻a∧◻b ◻a∧◻b≤◻b
    where

      ◻a≤◻a∧◻b : ◻ a ≤ ◻ a ∧ ◻ b
      ◻a≤◻a∧◻b = ≤-respʳ-≈ ◻a∧◻b≈◻a refl
        where
          a≈a∧b    = antisym (∧-greatest refl i) (x∧y≤x _ _)
          ◻a∧◻b≈◻a = Eq.trans (◻-resp-≈ a≈a∧b) ◻-distrib-∧

      ◻a∧◻b≤◻b : ◻ a ∧ ◻ b ≤ ◻ b
      ◻a∧◻b≤◻b = x∧y≤y (◻ a) (◻ b)

  CKBoxisMon : MonAlgebra
  CKBoxisMon = record
    { heytingAlgebra = heytingAlgebra
    ; ○_             = ◻_
    ; ○-resp-≈       = ◻-resp-≈
    ; ○-monotone     = ◻-monotone
    }

  open MonAlgebra CKBoxisMon using ()
    renaming (○-distrib-⊤-forth to ◻-distrib-⊤-forth)

  ◻-distrib-⊤ : {x y : Carrier} → ◻ ⊤ ≈ ⊤
  ◻-distrib-⊤ = antisym ◻-distrib-⊤-forth ◻-distrib-⊤-back

record SLAlgebra : Set₂ where
  field
    heytingAlgebra : HeytingAlgebra

  open HeytingAlgebra heytingAlgebra public

  field
    -- operator
    ◇_          : Carrier → Carrier
    ◇-resp-≈    : {x y : Carrier} → x ≈ y → ◇ x ≈ ◇ y

    -- structure of the operator
    ◇-monotone  : {x y : Carrier} → x ≤ y → ◇ x ≤ ◇ y
    x∧◇y≤◇⟨x∧y⟩ : {x y : Carrier} → x ∧ ◇ y ≤ ◇ (x ∧ y)

  SLisMon : MonAlgebra
  SLisMon = record
    { heytingAlgebra = heytingAlgebra
    ; ○_             = ◇_
    ; ○-resp-≈       = ◇-resp-≈
    ; ○-monotone     = ◇-monotone
    }
    
record PLLAlgebra : Set₂ where
  field
    heytingAlgebra : HeytingAlgebra

  open HeytingAlgebra heytingAlgebra public

  field
    -- operator
    ◇_          : Carrier → Carrier
    ◇-resp-≈    : {x y : Carrier} → x ≈ y → ◇ x ≈ ◇ y

    -- structure of the operator
    x≤◇x        : {x : Carrier} → x ≤ ◇ x
    ◇◇x≤◇x      : {x : Carrier} → ◇ ◇ x ≤ ◇ x
    ◇-distrib-∧ : {x y : Carrier} → ◇ (x ∧ y) ≈ ◇ x ∧ ◇ y

  ◇-distrib-∧-forth : {x y : Carrier} → ◇ (x ∧ y) ≤ ◇ x ∧ ◇ y
  ◇-distrib-∧-forth = ≤-respʳ-≈ ◇-distrib-∧ refl

  ◇-distrib-∧-back : {x y : Carrier} → ◇ x ∧ ◇ y ≤ ◇ (x ∧ y)
  ◇-distrib-∧-back = ≤-respˡ-≈ ◇-distrib-∧ refl

  ◇-idempotent : {x : Carrier} → ◇ ◇ x ≈ ◇ x
  ◇-idempotent = antisym ◇◇x≤◇x x≤◇x

  ◇-monotone : {a b : Carrier} → a ≤ b → ◇ a ≤ ◇ b
  ◇-monotone {a} {b} i = trans ◇a≤◇a∧◇b ◇a∧◇b≤◇b
    where

      ◇a≤◇a∧◇b : ◇ a ≤ ◇ a ∧ ◇ b
      ◇a≤◇a∧◇b = ≤-respʳ-≈ ◇a∧◇b≤◇a refl
        where
          a≈a∧b    = antisym (∧-greatest refl i) (x∧y≤x _ _)
          ◇a∧◇b≤◇a = Eq.trans (◇-resp-≈ a≈a∧b) ◇-distrib-∧

      ◇a∧◇b≤◇b : ◇ a ∧ ◇ b ≤ ◇ b
      ◇a∧◇b≤◇b = x∧y≤y (◇ a) (◇ b)

  x∧◇y≤◇⟨x∧y⟩ : {a b : Carrier} → a ∧ ◇ b ≤ ◇ (a ∧ b)
  x∧◇y≤◇⟨x∧y⟩ {a} {b} = trans (∧-greatest a∧◇b≤◇a a∧◇b≤◇b) ◇-distrib-∧-back
    where
    a∧◇b≤◇a : a ∧ ◇ b ≤ ◇ a
    a∧◇b≤◇a = trans (x∧y≤x a (◇ b)) x≤◇x
    a∧◇b≤◇b : a ∧ ◇ b ≤ ◇ b
    a∧◇b≤◇b = x∧y≤y a (◇ b)

  ◇-strong = x∧◇y≤◇⟨x∧y⟩
