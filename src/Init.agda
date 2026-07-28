{-# OPTIONS --safe --without-K #-}

module Init where

open import Relation.Binary.PropositionalEquality
  using  (_≡_)
  renaming
    ( refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
    ; cong to ≡-cong ; cong₂ to ≡-cong₂) public
    
open import Relation.Binary
  using (IsEquivalence) public
