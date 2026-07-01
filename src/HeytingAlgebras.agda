{-# OPTIONS --safe --without-K #-}

module HeytingAlgebras where

open import Level using (0ℓ ; suc)
open import Relation.Binary.Lattice.Bundles renaming (HeytingAlgebra to LHeytingAlgebra)

private 1ℓ = suc 0ℓ
HeytingAlgebra = LHeytingAlgebra 1ℓ 0ℓ 0ℓ
module HeytingAlgebra = LHeytingAlgebra

module HeytingAlgebraProperties (ℋ : HeytingAlgebra) where

  open HeytingAlgebra ℋ

  x∧y≤y∧x : (x y : Carrier) → x ∧ y ≤ y ∧ x
  x∧y≤y∧x x y = ∧-greatest (x∧y≤y x y) (x∧y≤x x y)

  ∧-assoc-forth : (x y z : Carrier) → (x ∧ y) ∧ z ≤ x ∧ (y ∧ z)
  ∧-assoc-forth x y z = ∧-greatest
    (trans (x∧y≤x (x ∧ y) z) (x∧y≤x x y))
    (∧-greatest (trans (x∧y≤x (x ∧ y) z) (x∧y≤y x y)) (x∧y≤y (x ∧ y) z))

------------------
-- Box algebras --
------------------

record CKBoxAlgebra : Set₂ where

  field
    ℋ : HeytingAlgebra

  open HeytingAlgebra ℋ public

  field
    -- operator
    ◻_          : Carrier → Carrier
    ◻-resp-≈    : {x y : Carrier} → x ≈ y → ◻ x ≈ ◻ y

    -- ◻ distributes over finite meets
    ◻-distrib-∧      : {x y : Carrier} → ◻ (x ∧ y) ≈ ◻ x ∧ ◻ y
    ◻-distrib-⊤-back : ⊤ ≤ ◻ ⊤

  ◻-distrib-∧-forth : {x y : Carrier} → ◻ (x ∧ y) ≤ ◻ x ∧ ◻ y
  ◻-distrib-∧-forth = ≤-respʳ-≈ ◻-distrib-∧ refl

  ◻-distrib-∧-back : {x y : Carrier} → ◻ x ∧ ◻ y ≤ ◻ (x ∧ y)
  ◻-distrib-∧-back = ≤-respˡ-≈ ◻-distrib-∧ refl

  ◻-distrib-⊤ : {x y : Carrier} → ◻ ⊤ ≈ ⊤
  ◻-distrib-⊤ = antisym (maximum _) ◻-distrib-⊤-back

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

record CS4BoxAlgebra : Set₂ where

  field
    ckBoxAlgebra : CKBoxAlgebra

  open CKBoxAlgebra ckBoxAlgebra public

  field
    -- deflationary
    ◻x≤x        : {x : Carrier} → ◻ x ≤ x

    -- inequality that implies idempotency
    ◻x≤◻◻x      : {x : Carrier} → ◻ x ≤ ◻ ◻ x

----------------------
-- Diamond algebras --
----------------------

record SLAlgebra : Set₂ where

  field
    ℋ : HeytingAlgebra

  open HeytingAlgebra ℋ public

  field
    -- operator
    ◇_          : Carrier → Carrier
    ◇-resp-≈    : {x y : Carrier} → x ≈ y → ◇ x ≈ ◇ y

    -- inequality that implies monotonicity
    ◇x≤◇⟨x∨y⟩   : {x y : Carrier} → ◇ x ≤ ◇ (x ∨ y)

    -- inequality corresponding to strength
    x∧◇y≤◇⟨x∧y⟩ : {x y : Carrier} → x ∧ ◇ y ≤ ◇ (x ∧ y)

  ◇-monotone : {a b : Carrier} → a ≤ b → ◇ a ≤ ◇ b
  ◇-monotone {a} {b} i = trans (◇x≤◇⟨x∨y⟩ {a} {b}) ◇⟨a∨b⟩≤◇b
    where
      a∨b≤b     = ∨-least i refl
      b≤a∨b     = y≤x∨y a b
      a∨b≈b     = antisym a∨b≤b b≤a∨b
      ◇⟨a∨b⟩≤◇b = ≤-respʳ-≈ (◇-resp-≈ a∨b≈b) refl

  open HeytingAlgebraProperties ℋ using (x∧y≤y∧x)

  ◇x∧y≤◇⟨x∧y⟩ : (x y : Carrier) → ◇ x ∧ y ≤ ◇ (x ∧ y)
  ◇x∧y≤◇⟨x∧y⟩ x y = trans (x∧y≤y∧x (◇ x) y)
    (trans (x∧◇y≤◇⟨x∧y⟩ {y} {x}) (◇-monotone (x∧y≤y∧x y x)))

record PLLAlgebra : Set₂ where

  field
    slAlgebra : SLAlgebra

  open SLAlgebra slAlgebra public

  field
    -- inflationary
    x≤◇x   : {x : Carrier} → x ≤ ◇ x

    -- inequality that implies idempotency
    ◇◇x≤◇x : {x : Carrier} → ◇ ◇ x ≤ ◇ x

  ◇-distrib-∧ : {x y : Carrier} → ◇ (x ∧ y) ≈ ◇ x ∧ ◇ y
  ◇-distrib-∧ {x} {y} = antisym ◇⟨x∧y⟩≤◇x∧◇y ◇x∧◇y≤◇⟨x∧y⟩
    where
      ◇⟨x∧y⟩≤◇x∧◇y : ◇ (x ∧ y) ≤ ◇ x ∧ ◇ y
      ◇⟨x∧y⟩≤◇x∧◇y = ∧-greatest
        (◇-monotone (x∧y≤x x y))
        (◇-monotone (x∧y≤y x y))

      ◇x∧◇y≤◇⟨x∧y⟩ : ◇ x ∧ ◇ y ≤ ◇ (x ∧ y)
      ◇x∧◇y≤◇⟨x∧y⟩ = trans (x∧◇y≤◇⟨x∧y⟩ {◇ x} {y})
        (trans (◇-monotone (◇x∧y≤◇⟨x∧y⟩ x y)) ◇◇x≤◇x)

------------------
-- IML Algebras --
------------------

record CMAlgebra : Set₂ where
  field
    ℋ       : HeytingAlgebra

  open HeytingAlgebra ℋ public

  field
    ⋆_          : Carrier → Carrier
    ⋆-resp-≈    : {x y : Carrier} → x ≈ y → ⋆ x ≈ ⋆ y
    ⋆-monotone  : {a b : Carrier} → a ≤ b → ⋆ a ≤ ⋆ b

record CKAlgebra : Set₂ where

  field
    𝒞 : CKBoxAlgebra

  open CKBoxAlgebra 𝒞 public

  field
    ◇_          : Carrier → Carrier
    ◇-resp-≈    : {x y : Carrier} → x ≈ y → ◇ x ≈ ◇ y

    -- implies monotonicity for ◇
    ◇x≤◇⟨x∨y⟩    : {x y : Carrier} → ◇ x ≤ ◇ (x ∨ y)

    -- enables validation of "◻ (φ → ψ) → (◇ φ → ◇ ψ)"
    ◻x∧◇y≤◇⟨x∧y⟩ : {x y : Carrier} → ◻ x ∧ ◇ y ≤ ◇ (x ∧ y)

record GCAlgebra : Set₂ where

  field
    ℋ : HeytingAlgebra

  open HeytingAlgebra ℋ public

  field
    -- operators
    ◻_          : Carrier → Carrier
    ◻-resp-≈    : {x y : Carrier} → x ≈ y → ◻ x ≈ ◻ y
    ◆_          : Carrier → Carrier
    ◆-resp-≈    : {x y : Carrier} → x ≈ y → ◆ x ≈ ◆ y

    -- ◻ distributes over finite meets
    ◻-distrib-∧      : {x y : Carrier} → ◻ (x ∧ y) ≈ ◻ x ∧ ◻ y
    ◻-distrib-⊤-back : ⊤ ≤ ◻ ⊤

    -- ◆ distributes over finite joins
    ◆-distrib-∨       : {x y : Carrier} → ◆ (x ∨ y) ≈ ◆ x ∨ ◆ y
    ◆-distrib-⊥-forth : ◆ ⊥ ≤ ⊥

    -- galois connection
    x≤◻◆x : {x : Carrier} → x ≤ ◻ ◆ x
    ◆◻x≤x : {x : Carrier} → ◆ ◻ x ≤ x

  ◻-distrib-∧-forth : {x y : Carrier} → ◻ (x ∧ y) ≤ ◻ x ∧ ◻ y
  ◻-distrib-∧-forth = ≤-respʳ-≈ ◻-distrib-∧ refl

  ◻-distrib-∧-back : {x y : Carrier} → ◻ x ∧ ◻ y ≤ ◻ (x ∧ y)
  ◻-distrib-∧-back = ≤-respˡ-≈ ◻-distrib-∧ refl

  ◻-distrib-⊤ : {x y : Carrier} → ◻ ⊤ ≈ ⊤
  ◻-distrib-⊤ = antisym (maximum _) ◻-distrib-⊤-back

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

  ◆-distrib-∨-forth : {x y : Carrier} → ◆ (x ∨ y) ≤ ◆ x ∨ ◆ y
  ◆-distrib-∨-forth = ≤-respʳ-≈ ◆-distrib-∨ refl

  ◆-distrib-∨-back : {x y : Carrier} → ◆ x ∨ ◆ y ≤ ◆ (x ∨ y)
  ◆-distrib-∨-back = ≤-respˡ-≈ ◆-distrib-∨ refl

  ◆-distrib-⊥ : {x y : Carrier} → ◆ ⊥ ≈ ⊥
  ◆-distrib-⊥ = antisym ◆-distrib-⊥-forth (minimum _)

  ◆-monotone : {a b : Carrier} → a ≤ b → ◆ a ≤ ◆ b
  ◆-monotone {a} {b} i = trans ◆a≤◆⟨a∨b⟩ ◆⟨a∨b⟩≤◆b
    where
      a∨b≤b     = ∨-least i refl
      b≤a∨b     = y≤x∨y a b
      a∨b≈b     = antisym a∨b≤b b≤a∨b
      ◆⟨a∨b⟩≤◆b = ≤-respʳ-≈ (◆-resp-≈ a∨b≈b) refl
      ◆a≤◆⟨a∨b⟩ = trans (x≤x∨y (◆ a) (◆ b)) ◆-distrib-∨-back

------------------------------------
-- Properties of Heyting Algebras --
------------------------------------

-- Has a monotonic operator
record HasMonOp (ℋ : HeytingAlgebra) : Set₂ where

  open HeytingAlgebra ℋ public

  field
    ⋆          : Carrier → Carrier
    ⋆-resp-≈   : {x y : Carrier} → x ≈ y → ⋆ x ≈ ⋆ y
    ⋆-monotone : {x y : Carrier} → x ≤ y → ⋆ x ≤ ⋆ y

  ⋆-distrib-∧-forth : {x y : Carrier} → ⋆ (x ∧ y) ≤ ⋆ x ∧ ⋆ y
  ⋆-distrib-∧-forth = ∧-greatest (⋆-monotone (x∧y≤x _ _)) (⋆-monotone (x∧y≤y _ _))

  ⋆-distrib-⊤-forth : ⋆ ⊤ ≤ ⊤
  ⋆-distrib-⊤-forth = maximum (⋆ ⊤)

  ⋆-distrib-∨-back : {x y : Carrier} → ⋆ x ∨ ⋆ y ≤ ⋆ (x ∨ y)
  ⋆-distrib-∨-back = ∨-least (⋆-monotone (x≤x∨y _ _)) (⋆-monotone (y≤x∨y _ _))

-- Has a nucleus/nuclear operator
record HasNucOp (ℋ : HeytingAlgebra) : Set₂ where

  open HeytingAlgebra ℋ public

  field
    -- operator
    ◇_          : Carrier → Carrier
    ◇-resp-≈    : {x y : Carrier} → x ≈ y → ◇ x ≈ ◇ y

    -- inflationary
    x≤◇x        : {x : Carrier} → x ≤ ◇ x

    -- inequality that implies idempotency
    ◇◇x≤◇x      : {x : Carrier} → ◇ ◇ x ≤ ◇ x

    -- inequality that implies meet-preservation
    ◇-distrib-∧ : {x y : Carrier} → ◇ (x ∧ y) ≈ ◇ x ∧ ◇ y

  ◇-distrib-∧-forth : {x y : Carrier} → ◇ (x ∧ y) ≤ ◇ x ∧ ◇ y
  ◇-distrib-∧-forth = ≤-respʳ-≈ ◇-distrib-∧ refl

  ◇-distrib-∧-back : {x y : Carrier} → ◇ x ∧ ◇ y ≤ ◇ (x ∧ y)
  ◇-distrib-∧-back = ≤-respˡ-≈ ◇-distrib-∧ refl

  ◇-distrib-⊤ : {x y : Carrier} → ◇ ⊤ ≈ ⊤
  ◇-distrib-⊤ = antisym (maximum _) x≤◇x

  ◇-idempotent : {x : Carrier} → ◇ ◇ x ≈ ◇ x
  ◇-idempotent = antisym ◇◇x≤◇x x≤◇x

  ◇-monotone : {a b : Carrier} → a ≤ b → ◇ a ≤ ◇ b
  ◇-monotone {a} {b} i = trans ◇a≤◇a∧◇b ◇a∧◇b≤◇b
    where

      ◇a≤◇a∧◇b : ◇ a ≤ ◇ a ∧ ◇ b
      ◇a≤◇a∧◇b = ≤-respʳ-≈ ◇a∧◇b≈◇a refl
        where
          a≈a∧b    = antisym (∧-greatest refl i) (x∧y≤x _ _)
          ◇a∧◇b≈◇a = Eq.trans (◇-resp-≈ a≈a∧b) ◇-distrib-∧

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

module Properties where

  module _ (𝒜 : PLLAlgebra) where

    open PLLAlgebra 𝒜

    PLLAlgebraIsNuclear : HasNucOp ℋ
    PLLAlgebraIsNuclear = record
      { ◇_          = ◇_
      ; ◇-resp-≈    = ◇-resp-≈
      ; x≤◇x        = x≤◇x
      ; ◇◇x≤◇x      = ◇◇x≤◇x
      ; ◇-distrib-∧ = ◇-distrib-∧
      }

  module _ {ℋ : HeytingAlgebra} (hasNucOp : HasNucOp ℋ) where

    open HasNucOp hasNucOp

    nucSLAlgebra : SLAlgebra
    nucSLAlgebra = record
      { ℋ              = ℋ
      ; ◇_             = ◇_
      ; ◇-resp-≈       = ◇-resp-≈
      ; ◇x≤◇⟨x∨y⟩      = ◇-monotone (x≤x∨y _ _)
      ; x∧◇y≤◇⟨x∧y⟩    = x∧◇y≤◇⟨x∧y⟩
      }

    nucPLLAlgebra : PLLAlgebra
    nucPLLAlgebra = record
      { slAlgebra = nucSLAlgebra
      ; x≤◇x      = x≤◇x
      ; ◇◇x≤◇x    = ◇◇x≤◇x
      }
