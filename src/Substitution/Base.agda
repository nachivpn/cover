{-# OPTIONS --safe --without-K #-}

import Context.Base as Context

-- Substitutions (parameterized by terms `Tm` and modal accessibility relation `Acc`)
-------------------------------------------------------------------------------------

module Substitution.Base
  (Ty          : Set)
  (let open Context Ty using (Ctx ; _⊑_ ; Var))
  (Tm          : (Γ : Ctx) → (a : Ty) → Set)
  (var         : {Γ : Ctx} → {a : Ty} → (v : Var Γ a) → Tm Γ a)
  (wkTm        : {Γ' Γ : Ctx} → {a : Ty} → (w : Γ ⊑ Γ') → (t : Tm Γ a) → Tm Γ' a)
  where

  -- "Cannot use generalized variable from let-opened module"
  open Context Ty hiding (Ctx ; _⊑_ ; Var)

  private
    variable
      a b c d : Ty

  data Sub : Ctx → Ctx → Set where
    []   : Sub Δ []
    _`,_ : (σ : Sub Δ  Γ) → (t : Tm Δ a)      → Sub Δ (Γ `, a)

  Sub- : Ctx → Ctx → Set
  Sub- Δ Γ = Sub Γ Δ

  variable
    s s' s'' : Sub Δ Γ
    σ σ' σ'' : Sub Δ Γ
    τ τ' τ'' : Sub Δ Γ

  -- composition operation for weakening after substitution
  trimSub : Δ ⊑ Γ → Sub Γ' Γ → Sub Γ' Δ
  trimSub base      []         = []
  trimSub (drop w)  (s `, x)   = trimSub w s
  trimSub (keep w)  (s `, x)   = (trimSub w s) `, x

  -- apply substitution to a variable
  substVar : Sub Γ Δ → Var Δ a → Tm Γ a
  substVar (s `, t)  zero     = t
  substVar (s `, _t) (succ v) = substVar s v

  -- weaken a substitution
  wkSub : Γ ⊑ Γ' → Sub Γ Δ → Sub Γ' Δ
  wkSub w []         = []
  wkSub w (s `, t)   = wkSub w s `, wkTm w t

  -- NOTE: composition requires parallel substitution for terms

  -- "drop" the last variable in the context
  dropˢ : Sub Γ Δ → Sub (Γ `, a) Δ
  dropˢ s = wkSub freshWk s

  -- "keep" the last variable in the context
  keepˢ : Sub Γ Δ → Sub (Γ `, a) (Δ `, a)
  keepˢ s = dropˢ s `, var zero

  -- embed a weakening to substitution
  embWk : Δ ⊑ Γ → Sub Γ Δ
  embWk base      = []
  embWk (drop  w) = dropˢ  (embWk w)
  embWk (keep  w) = keepˢ  (embWk w)

  -- identity substitution
  idˢ : Sub Γ Γ
  idˢ = embWk ⊑-refl

  idˢ[_] = λ Γ → idˢ {Γ}

  module Composition
    (substTm     : {Δ Γ : Ctx} → {a : Ty} → (σ : Sub Δ Γ) → (t : Tm Γ a) → Tm Δ a)
    where

    infixr 20 _∙ˢ_

    -- substitution composition
    _∙ˢ_ : Sub Δ Γ → Sub Δ' Δ → Sub Δ' Γ
    []        ∙ˢ s = []
    (s' `, t) ∙ˢ s = (s' ∙ˢ s) `, substTm s t
