{-# OPTIONS --safe --without-K #-}

module Init where

open import Relation.Binary.PropositionalEquality
  using  (_≡_)
  renaming
    ( refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
    ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst) public
    
open import Relation.Binary
  using (IsEquivalence) public

open import Categories.Category.Core renaming (Category to LCategory)
open import Level using (0ℓ)
Category = LCategory 0ℓ 0ℓ 0ℓ
module Category = LCategory
