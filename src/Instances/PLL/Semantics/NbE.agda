{-# OPTIONS --safe --without-K #-}

module Instances.PLL.Semantics.NbE where

open import Instances.PLL.System
open import Instances.PLL.Semantics.Entailment
import Instances.PLL.Semantics.Interpretation as Interpretation
import Instances.PLL.Semantics.Soundness as Soundness

open import Neighborhood.Systems 𝕎

open import Function using (_∘_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Product
  using (Σ ; ∃ ; ∃₂ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)

data _⊢Ne_ : Ctx → Form → Set
data _⊢Nf_ : Ctx → Form → Set

data _⊢Ne_ where
  hyp   : Var Γ a → Γ ⊢Ne a
  ⇒-E   : Γ ⊢Ne (a ⇒ b) → Γ ⊢Nf a → Γ ⊢Ne b
  ∧-E1  : Γ ⊢Ne (a ∧ b) → Γ ⊢Ne a
  ∧-E2  : Γ ⊢Ne (a ∧ b) → Γ ⊢Ne b

data _⊢Nf_ where
  emb   : Γ ⊢Ne (𝕡 i) → Γ ⊢Nf (𝕡 i)
  ⊤-I   : Γ ⊢Nf ⊤
  ⊥-E   : Γ ⊢Ne ⊥ → Γ ⊢Nf a
  ⇒-I   : (Γ `, a) ⊢Nf b → Γ ⊢Nf (a ⇒ b)
  ∧-I   : Γ ⊢Nf a → Γ ⊢Nf b → Γ ⊢Nf (a ∧ b)
  ∨-I1  : Γ ⊢Nf a → Γ ⊢Nf (a ∨ b)
  ∨-I2  : Γ ⊢Nf b → Γ ⊢Nf (a ∨ b)
  ∨-E   : Γ ⊢Ne (a ∨ b) → (Γ `, a) ⊢Nf c → (Γ `, b) ⊢Nf c → Γ ⊢Nf c
  ◇-I   : Γ ⊢Nf a → Γ ⊢Nf (◇ a)
  ◇-B   : Γ ⊢Ne (◇ a) → (Γ `, a) ⊢Nf (◇ b) → Γ ⊢Nf (◇ b)

wkNe : Γ ⊑ Γ' → Γ ⊢Ne a → Γ' ⊢Ne a
wkNf : Γ ⊑ Γ' → Γ ⊢Nf a → Γ' ⊢Nf a

wkNe i (hyp x)   = hyp (wkVar i x)
wkNe i (⇒-E n x) = ⇒-E (wkNe i n) (wkNf i x)
wkNe i (∧-E1 n)  = ∧-E1 (wkNe i n)
wkNe i (∧-E2 n)  = ∧-E2 (wkNe i n)

wkNf i (emb x)       = emb (wkNe i x)
wkNf i ⊤-I           = ⊤-I
wkNf i (⊥-E x)       = ⊥-E (wkNe i x)
wkNf i (⇒-I n)       = ⇒-I (wkNf (keep i) n)
wkNf i (∧-I n m)     = ∧-I (wkNf i n) (wkNf i m)
wkNf i (∨-I1 n)      = ∨-I1 (wkNf i n)
wkNf i (∨-I2 n)      = ∨-I2 (wkNf i n)
wkNf i (∨-E n m1 m2) = ∨-E (wkNe i n) (wkNf (keep i) m1) (wkNf (keep i) m2)
wkNf i (◇-I m)       = ◇-I (wkNf i m)
wkNf i (◇-B n m)     = ◇-B (wkNe i n) (wkNf (keep i) m)

embNe : Γ ⊢Ne a → Γ ⊢ a
embNf : Γ ⊢Nf a → Γ ⊢ a

embNe (hyp x)   = hyp x
embNe (⇒-E x n) = ⇒-E (embNe x) (embNf n)
embNe (∧-E1 x)  = ∧-E1 (embNe x)
embNe (∧-E2 x)  = ∧-E2 (embNe x)

embNf (emb x) = embNe x
embNf ⊤-I         = ⊤-I
embNf (⊥-E x)     = ⊥-E (embNe x)
embNf (⇒-I n)     = ⇒-I (embNf n)
embNf (∧-I n m)   = ∧-I (embNf n) (embNf m)
embNf (∨-I1 n)    = ∨-I1 (embNf n)
embNf (∨-I2 n)    = ∨-I2 (embNf n)
embNf (∨-E x n m) = ∨-E (embNe x) (embNf n) (embNf m)
embNf (◇-I m)     = ◇-I (embNf m)
embNf (◇-B n m)   = ◇-B (embNe n) (embNf m)

-----------------------
-- Base cover system --
-----------------------

open IPLBaseSystem ⊥ _∨_ _⊢Ne_ wkNe

-------------------------
-- Lax modality system --
-------------------------

data K◇ : Ctx → Set where
  leaf    : (Γ : Ctx) → K◇ Γ
  dead    : Γ ⊢Ne ⊥ → K◇ Γ
  cons    : Γ ⊢Ne (◇ a) → K◇ (Γ `, a) → K◇ Γ
  branch  : Γ ⊢Ne (a ∨ b) → K◇ (Γ `, a) → K◇ (Γ `, b) → K◇ Γ

data _∈◇_ (Δ : Ctx) : K◇ Γ → Set where
  here  : Δ ∈◇ leaf Δ
  there : {n : Γ ⊢Ne (◇ a)} {k : K◇ (Γ `, a)} → Δ ∈◇ k → Δ ∈◇ cons n k
  left  : {n : Γ ⊢Ne (a ∨ b)} {k : K◇ (Γ `, a)} {k' : K◇ (Γ `, b)}
    → Δ ∈◇ k → Δ ∈◇ branch n k k'
  right : {n : Γ ⊢Ne (a ∨ b)} {k : K◇ (Γ `, a)} {k' : K◇ (Γ `, b)}
    → Δ ∈◇ k' → Δ ∈◇ branch n k k'

open import Neighborhood.Lib 𝕎 K◇ _∈◇_ using ()
    renaming (∣_∣ to ∣_∣◇ ; ForAllW to ForAllW◇) public

wkK◇ : Γ ⊑ Γ' → K◇ Γ → K◇ Γ'
wkK◇ i (leaf Δ)        = leaf _
wkK◇ i (dead n)        = dead (wkNe i n)
wkK◇ i (cons n k)      = cons (wkNe i n) (wkK◇ (keep i) k)
wkK◇ i (branch n k k') = branch (wkNe i n) (wkK◇ (keep i) k) (wkK◇ (keep i) k')

wkK◇-ref : (i : Γ ⊑ Γ') (k : K◇ Γ) → ∣ k ∣◇ ≼ ∣ wkK◇ i k ∣◇
wkK◇-ref i (leaf _) here
  = _ , here , i
wkK◇-ref i (dead x) ()
wkK◇-ref i (cons n k) (there p)
  = let (Δ , p' , i') = wkK◇-ref (keep i) k p in
     (Δ , there p' , i')
wkK◇-ref i (branch x k1 k2) (left p)
  = let (Δ , p' , i') = wkK◇-ref (keep i) k1 p in
     (Δ , left p' , i')
wkK◇-ref i (branch x k1 k2) (right p)
  = let (Δ , p' , i') = wkK◇-ref (keep i) k2 p in
     (Δ , right p' , i')

K◇-ref : (k : K◇ Γ) → ∣ k ∣◇ ⊆ (↑ Γ)
K◇-ref (leaf _)         here
  = ⊑-refl
K◇-ref (dead x)         ()
K◇-ref (cons n k)       (there p)
  = freshWk ∙ K◇-ref k p
K◇-ref (branch x k1 k2) (left p)
  = freshWk ∙ K◇-ref k1 p
K◇-ref (branch x k1 k2) (right p)
  = freshWk ∙ K◇-ref k2 p

idK◇ : (Γ : Ctx) → K◇ Γ
idK◇ = leaf

idK◇-sub : ∣ idK◇ Γ ∣◇ ⊆ ⟨ Γ ⟩
idK◇-sub here = ≡-refl
  
transK◇ : (k : K◇ Γ) → ForAllW◇ k K◇ → K◇ Γ
transK◇ (leaf _)        f = f here
transK◇ (dead x)        f = dead x
transK◇ (cons n k)      f = cons n (transK◇ k (f ∘ there))
transK◇ (branch x k k') f = branch x (transK◇ k (f ∘ left)) (transK◇ k' (f ∘ right))

transK◇-sub : (k : K◇ Γ) (h : ForAllW◇ k K◇)
  → ∣ (transK◇ k h) ∣◇ ⊆ ⨆ ∣ k ∣◇ (∣_∣◇ ∘ h)
transK◇-sub (leaf Γ)        h p
  = (Γ , here) , p
transK◇-sub (dead x)        h ()
transK◇-sub (cons n k)      h (there p) = 
  let (v' , p') , pl = transK◇-sub k (h ∘ there) p
  in (v' , there p') , pl
transK◇-sub (branch x k k') h (left p)  =
  let (vl , p') , pl = transK◇-sub k (h ∘ left) p
  in (vl , left p') , pl
transK◇-sub (branch x k k') h (right p) =
  let (vl , p') , pr = transK◇-sub k' (h ∘ right) p
  in (vl , right p') , pr

NS◇ : NeighborhoodSystem
NS◇ = record
  { N          = K◇
  ; _∈_        = _∈◇_
  ; refinement = record { wkN = wkK◇ ; wkN-ref = wkK◇-ref }
  }

CS◇ : CoverSystem NS◇
CS◇ = record
  { inclusion    = record { N-ref = K◇-ref }
  ; identity     = record { idN[_] = idK◇ ; idN-sub = idK◇-sub }
  ; transitivity = record { transN = transK◇ ; transN-sub = transK◇-sub }
  }

WCS◇ : WeakCoverSystem NS◇
WCS◇ = CoverSystem.weakCoverSystem CS◇

-- imports ◇', etc.
open import USet.Lax.PLL.Cover 𝕎 WCS◇

------------------------
-- Modal Localization --
------------------------

inclK◇ : K₊ Γ → K◇ Γ
inclK◇ (leaf _)        = leaf _
inclK◇ (dead x)        = dead x
inclK◇ (branch x k k') = branch x (inclK◇ k) (inclK◇ k')

inclK◇-sub : (k : K₊ Γ) → ∣ inclK◇ k ∣◇ ⊆ ∣ k ∣₊
inclK◇-sub (leaf _)        here      = here
inclK◇-sub (branch x k k') (left p)  = left (inclK◇-sub k p)
inclK◇-sub (branch x k k') (right p) = right (inclK◇-sub k' p)

incl' : {A : USet} → 𝒥' A →̇ ◇' A
incl' {A = A} .apply (k₊ , f) = inclK◇ k₊ , ⊆-trans {Z = A ₀_} (inclK◇-sub k₊) f

◇'-localize : {A : USet} → 𝒥' (◇' A) →̇ ◇' (𝒥' A)
◇'-localize {A} = (◇'-map (𝒥'-point {A}) ∘' ◇'-join {A}) ∘' incl' {◇' A} 

open LocalizedCover WCS₊ (λ {A} → ◇'-localize {A = A}) renaming (LUSetPLLA to ℛ)

------------------------
-- Model construction --
------------------------

Nf' : Form → USet
Nf' a = uset (_⊢Nf a) wkNf

Ne' : Form → USet
Ne' a = uset (_⊢Ne a) wkNe

emb' : Ne' (𝕡 i) →̇ Nf' (𝕡 i)
emb' .apply = emb

∨-I1' : Nf' a →̇ Nf' (a ∨ b)
∨-I1' .apply = ∨-I1

∨-I2' : Nf' b →̇ Nf' (a ∨ b)
∨-I2' .apply = ∨-I2

Nf₊ : Form → LUSet
Nf₊ a = luset (Nf' a) (run𝒥' {Nf' a} localizeNf)
  where
  localizeNf : (k : K₊ Γ) → ForAllW₊ k (_⊢Nf a) → Γ ⊢Nf a
  localizeNf (leaf _)         h = h here
  localizeNf (dead x)         h = ⊥-E x
  localizeNf (branch x k1 k2) h = ∨-E x (localizeNf k1 (h ∘ left)) (localizeNf k2 (h ∘ right))

open Interpretation ℛ (Nf₊ ∘ 𝕡) -- imports ⟦-⟧
open LUSet -- imports localize and 𝒳

---------------------
-- Residualization --
---------------------

◇'-collect : ◇' (Nf' a) →̇ Nf' (◇ a)
◇'-collect {a = a} = ◇'-run {Nf' a} collectAux
  where
  collectAux : (k : K◇ Γ) (f : ForAllW◇ k (Nf' a ₀_)) → Nf' (◇ a) ₀ Γ
  collectAux (leaf _)        f = ◇-I (f here)
  collectAux (dead x)        f = ⊥-E x
  collectAux (cons x k)      f = ◇-B x (collectAux k (f ∘ there))
  collectAux (branch x k k') f = ∨-E x (collectAux k (f ∘ left)) (collectAux k' (f ∘ right))

reify   : ∀ a → 𝒳 ⟦ a ⟧ →̇ (Nf' a)
reflect : ∀ a → Ne' a →̇ 𝒳 ⟦ a ⟧

reify (𝕡 i)   = id'
reify ⊤       = fun (λ _ → ⊤-I)
reify (a ⇒ b) = fun λ x → ⇒-I (reify b .apply (x freshWk (reflect a .apply (hyp zero))))
reify (a ∧ b) = fun λ x → ∧-I (reify a .apply (proj₁ x)) (reify b .apply (proj₂ x))
reify ⊥       = Nf₊ ⊥ .localize ∘' map𝒥' (⊥'-elim {Nf' ⊥})
reify (a ∨ b) = Nf₊ (a ∨ b) .localize ∘' map𝒥' [ ∨-I1' ∘' reify a  , ∨-I2' ∘' reify b ]'
reify (◇ a)   = ◇'-collect ∘' ◇'-map (reify a)

reflect (𝕡 i)   = emb'
reflect ⊤       = unit'
reflect (a ⇒ b) = fun λ n i x → reflect b .apply (⇒-E (wkNe i n) (reify a .apply x))
reflect (a ∧ b) = fun λ n → reflect a .apply (∧-E1 n) , reflect b .apply (∧-E2 n)
reflect ⊥       = fun λ n → dead n , λ{()}
reflect (a ∨ b) = fun λ n → branch n (leaf (_ `, a)) (leaf (_ `, b)) ,
  λ { (left here)  → inj₁ (reflect a .apply (hyp zero))
    ; (right here) → inj₂ (reflect b .apply (hyp zero))
    }
reflect (◇ a)   = fun λ n → cons n (leaf (_ `, a)) ,
  λ { (there here) → reflect a .apply (hyp zero) }

---------
-- NbE --
---------

idEnv : ∀ Γ → ⟦ Γ ⟧c .𝒳 ₀ Γ
idEnv []       = _
idEnv (Γ `, a) = wk (⟦ Γ ⟧c .𝒳) freshWk (idEnv Γ) , reflect a .apply (hyp zero)

quot : (⟦ Γ ⟧c →̇₊ ⟦ a ⟧) → Γ ⊢Nf a
quot {Γ} {a} f = reify a .apply (f .apply (idEnv Γ))

nbe : Γ ⊢ a → Γ ⊢Nf a
nbe t = let open Soundness.Proof ℛ (Nf₊ ∘ 𝕡) in quot (⟦-⟧-sound t)

completeness : Γ ⊨ a → Γ ⊢ a
completeness f = embNf (quot (f ℛ (Nf₊ ∘ 𝕡)))

