{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.STPC.TermModel where

open import Init
    
open import Instances.LatLog.STPC.Calculus
open import Instances.LatLog.STPC.Conversion

infix 19 _∼>_

_∼>_ : Ty → Ty → Set
a ∼> b = Tm [ a ] b

[_]ˢ : Tm Γ a → Sub Γ [ a ]
[ t ]ˢ = [] `, t

[-]ˢ-pres-≈ : t ≈ t' → [ t ]ˢ ≈ˢ [ t' ]ˢ
[-]ˢ-pres-≈ t≈t' = [] `, t≈t'

v0ᵗ[_] : (a : Ty) → Tm (Γ `, a) a
v0ᵗ[ _ ] = var v0

v0ᵗ : Tm (Γ `, a) a
v0ᵗ = v0ᵗ[ _ ]

∼>-refl[_] = v0ᵗ[_]

id[_]  = v0ᵗ[_]

id : a ∼> a
id = v0ᵗ

∼>-trans : a ∼> b → b ∼> c → a ∼> c
∼>-trans t u = substTm [ t ]ˢ u

infix 21 _⟨_⟩

_⟨_⟩ :  b ∼> c → a ∼> b → a ∼> c
u ⟨ t ⟩ = ∼>-trans t u

⟨-⟩-pres-≈ : t ≈ t' → u ≈ u' → t ⟨ u ⟩ ≈ t' ⟨ u' ⟩
⟨-⟩-pres-≈  t≈t' u≈u' = substTm-pres-≈ ([-]ˢ-pres-≈ u≈u') t≈t'

⟨-⟩-unit-right : (a : Ty) {b : Ty} (t : a ∼> b) → t ⟨ id ⟩ ≈ t
⟨-⟩-unit-right _ t = ≡-to-≈ (substTm-pres-idˢ t)

⟨-⟩-unit-left : {a : Ty} (b : Ty) (t : a ∼> b) → id ⟨ t ⟩ ≈ t
⟨-⟩-unit-left _ _ = ≈-refl

⟨-⟩-assoc : (t : c ∼> d) (u : b ∼> c) (u' : a ∼> b) → (t ⟨ u ⟩) ⟨ u' ⟩ ≈ t ⟨ u ⟨ u' ⟩ ⟩
⟨-⟩-assoc t u u' = ≡-to-≈ ((≡-sym (substTm-pres-∙ˢ [ u ]ˢ [ u' ]ˢ t)))

⟦_⟧ : Ctx → Ty
⟦ [] ⟧     = 𝟙
⟦ Γ `, a ⟧ = ⟦ Γ ⟧ × a

-- "context term" (c.f. Lemma 3.1 in [Clouston 2018])
cᵗ[_] : ∀ Γ → Tm Γ ⟦ Γ ⟧
cᵗ[ [] ]     = unit
cᵗ[ Γ `, a ] = pair (wkTm freshWk cᵗ[ Γ ]) (var zero)

from-∼> : ⟦ Γ ⟧ ∼> a → Tm Γ a
from-∼> = substTm ([] `, cᵗ[ _ ])

from-∼>-pres-≈ : {t' u' : ⟦ Γ ⟧ ∼> a} → t' ≈ u' → from-∼> t' ≈ from-∼> u'
from-∼>-pres-≈ = substTm-pres-≈-right _


