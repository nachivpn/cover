{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.STPC.TermModel where

open import Init
    
open import Instances.LatLog.STPC.Calculus
open import Instances.LatLog.STPC.Conversion

infix 19 _∼>_

_∼>_ : Ty → Ty → Set
a ∼> b = Tm [ a ] b

[_]ₛ : Tm Γ a → Sub Γ [ a ]
[ t ]ₛ = [] `, t

[-]ₛ-pres-≈ : t ≈ t' → [ t ]ₛ ≈ₛ [ t' ]ₛ
[-]ₛ-pres-≈ t≈t' = [] `, t≈t'

v0ₜ[_] : (a : Ty) → Tm (Γ `, a) a
v0ₜ[ _ ] = var v0

v0ₜ : Tm (Γ `, a) a
v0ₜ = v0ₜ[ _ ]

∼>-refl[_] = v0ₜ[_]

id[_]  = v0ₜ[_]

id : a ∼> a
id = v0ₜ

∼>-trans : a ∼> b → b ∼> c → a ∼> c
∼>-trans t u = substTm [ t ]ₛ u

infix 21 _⟨_⟩

_⟨_⟩ :  b ∼> c → a ∼> b → a ∼> c
u ⟨ t ⟩ = ∼>-trans t u

⟨-⟩-pres-≈ : t ≈ t' → u ≈ u' → t ⟨ u ⟩ ≈ t' ⟨ u' ⟩
⟨-⟩-pres-≈  t≈t' u≈u' = substTm-pres-≈ ([-]ₛ-pres-≈ u≈u') t≈t'

⟨-⟩-unit-right : (a : Ty) {b : Ty} (t : a ∼> b) → t ⟨ id ⟩ ≈ t
⟨-⟩-unit-right _ t = ≡-to-≈ (substTm-pres-idₛ t)

⟨-⟩-unit-left : {a : Ty} (b : Ty) (t : a ∼> b) → id ⟨ t ⟩ ≈ t
⟨-⟩-unit-left _ _ = ≈-refl

⟨-⟩-assoc : (t : c ∼> d) (u : b ∼> c) (u' : a ∼> b) → (t ⟨ u ⟩) ⟨ u' ⟩ ≈ t ⟨ u ⟨ u' ⟩ ⟩
⟨-⟩-assoc t u u' = ≡-to-≈ ((≡-sym (substTm-pres-∙ₛ [ u ]ₛ [ u' ]ₛ t)))

⟦_⟧ : Ctx → Ty
⟦ [] ⟧     = 𝟙
⟦ Γ `, a ⟧ = ⟦ Γ ⟧ × a

-- "context term" (c.f. Lemma 3.1 in [Clouston 2018])
cₜ[_] : ∀ Γ → Tm Γ ⟦ Γ ⟧
cₜ[ [] ]     = unit
cₜ[ Γ `, a ] = pair (wkTm freshWk cₜ[ Γ ]) (var zero)

from-∼> : ⟦ Γ ⟧ ∼> a → Tm Γ a
from-∼> = substTm ([] `, cₜ[ _ ])

from-∼>-pres-≈ : {t' u' : ⟦ Γ ⟧ ∼> a} → t' ≈ u' → from-∼> t' ≈ from-∼> u'
from-∼>-pres-≈ = substTm-pres-≈-right _


