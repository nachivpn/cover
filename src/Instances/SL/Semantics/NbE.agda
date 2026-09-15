{-# OPTIONS --safe --without-K #-}

module Instances.SL.Semantics.NbE where

open import Instances.SL.System
open import Instances.SL.Semantics.Entailment
import Instances.SL.Semantics.Interpretation as Interpretation
import Instances.SL.Semantics.Soundness as Soundness

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
  ◇-M   : Γ ⊢Ne (◇ a) → (Γ `, a) ⊢Nf b → Γ ⊢Nf (◇ b)

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
wkNf i (◇-M n m)     = ◇-M (wkNe i n) (wkNf (keep i) m)

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
embNf (◇-M n m)   = ◇-M (embNe n) (embNf m)

-----------------------
-- Base cover system --
-----------------------

open IPLBaseSystem ⊥ _∨_ _⊢Ne_ wkNe

-------------------------
-- Lax modality system --
-------------------------

data K◇ : Ctx → Set where
  single  : Γ ⊢Ne (◇ a) → K◇ Γ
  dead    : Γ ⊢Ne ⊥ → K◇ Γ
  branch  : Γ ⊢Ne (a ∨ b) → K◇ (Γ `, a) → K◇ (Γ `, b) → K◇ Γ

data _∈◇_  : Ctx → {Γ : Ctx} → K◇ Γ → Set where
  here  : {n : Γ ⊢Ne (◇ a)} → (Γ `, a) ∈◇ single n
  left  : {n : Γ ⊢Ne (a ∨ b)} {k : K◇ (Γ `, a)} {k' : K◇ (Γ `, b)}
    → Δ ∈◇ k → Δ ∈◇ branch n k k'
  right : {n : Γ ⊢Ne (a ∨ b)} {k : K◇ (Γ `, a)} {k' : K◇ (Γ `, b)}
    → Δ ∈◇ k' → Δ ∈◇ branch n k k'

open import Neighborhood.Lib 𝕎 K◇ _∈◇_ using () 
  renaming (∣_∣ to ∣_∣◇ ; ForAllW to ForAllW◇)
           
wkK◇ : Γ ⊑ Γ' → K◇ Γ → K◇ Γ'
wkK◇ i (single n)      = single (wkNe i n)
wkK◇ i (dead n)        = dead (wkNe i n)
wkK◇ i (branch n k k') = branch (wkNe i n) (wkK◇ (keep i) k) (wkK◇ (keep i) k')

wkK◇-ref : (i : Γ ⊑ Γ') (k : K◇ Γ) → ∣ k ∣◇ ≼ ∣ wkK◇ i k ∣◇
wkK◇-ref i (single n) here
  = (-, here , keep i)
wkK◇-ref i (dead x) ()
wkK◇-ref i (branch x k1 k2) (left p)
  = let (Δ , p' , i') = wkK◇-ref (keep i) k1 p in
     (Δ , left p' , i')
wkK◇-ref i (branch x k1 k2) (right p)
  = let (Δ , p' , i') = wkK◇-ref (keep i) k2 p in
     (Δ , right p' , i')

K◇-ref : (k : K◇ Γ) → ∣ k ∣◇ ⊆ (↑ Γ)
K◇-ref (single n)       here
  = freshWk
K◇-ref (dead n)         ()
K◇-ref (branch x k1 k2) (left p)
  = freshWk ∙ K◇-ref k1 p
K◇-ref (branch x k1 k2) (right p)
  = freshWk ∙ K◇-ref k2 p

NS◇ : NeighborhoodSystem
NS◇ = record
  { N          = K◇
  ; _∈_        = _∈◇_
  ; refinement = record { wkN = wkK◇ ; wkN-ref = wkK◇-ref }
  }

SLMS◇ : SLModalSystem NS◇
SLMS◇ = record { inclusion = record { N-ref = K◇-ref } }

-- imports ◇', etc.
open import USet.Lax.SL.Cover 𝕎 SLMS◇

------------------------
-- Modal Localization --
------------------------

transK₊◇ : (k : K₊ Γ) → ForAllW₊ k K◇ → K◇ Γ
transK₊◇ (leaf _)         f = f here
transK₊◇ (dead x)         f = dead x
transK₊◇ (branch x k1 k2) f = branch x
  (transK₊◇ k1 (f ∘ left))
  (transK₊◇ k2 (f ∘ right))

transK₊◇-bwd-member : (k : K₊ Γ) (h : ForAllW₊ k K◇)
  → ∣ transK₊◇ k h ∣◇ ⊆ ⨆ ∣ k ∣₊ (∣_∣◇ ∘ h)
transK₊◇-bwd-member (leaf Γ)       f p
  = (Γ , here) , p
transK₊◇-bwd-member (branch x k1 k2) f (left p)
  = let (Χ , p) , q = transK₊◇-bwd-member k1 (f ∘ left) p
    in (Χ , left p) , q
transK₊◇-bwd-member (branch x k1 k2) f (right p)
  = let (Χ , p) , q = transK₊◇-bwd-member k2 (f ∘ right) p
    in (Χ , right p) , q

◇'-localize-imm : {A : USet} → 𝒥' (◇' A) →̇ ◇' A
◇'-localize-imm .apply (k , fam) = transK₊◇ k (proj₁ ∘ fam) , λ x →
  let (x , y) , z = transK₊◇-bwd-member k (proj₁ ∘ fam) x in (proj₂ ∘ fam) y z

◇'-localize : {A : USet} → 𝒥' (◇' A) →̇ ◇' (𝒥' A)
◇'-localize {A} = ◇'-map {A} {𝒥' A} 𝒥'-point ∘' ◇'-localize-imm {A}

open LocalizedCover WCS₊ (λ {A} → ◇'-localize {A}) renaming (LUSetSLA to ℛ)

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
  collectAux (single x)      f = ◇-M x (f here)
  collectAux (dead x)        f = ⊥-E x
  collectAux (branch x k k') f = ∨-E x (collectAux k (f ∘ left)) (collectAux k' (f ∘ right))

◇'-register : Ne' (◇ a) →̇ ◇' (Ne' a)
◇'-register {a} .apply {Γ} n = single n , λ { here → hyp zero }


reify   : ∀ a → 𝒳 ⟦ a ⟧ →̇ (Nf' a)
reflect : ∀ a → Ne' a →̇ 𝒳 ⟦ a ⟧

reify (𝕡 i)   = id'
reify ⊤       = fun (λ _ → ⊤-I)
reify (a ⇒ b) = fun λ x → ⇒-I (reify b .apply (x freshWk (reflect a .apply (hyp zero))))
reify (a ∧ b) = fun λ x → ∧-I (reify a .apply (proj₁ x)) (reify b .apply (proj₂ x))
reify ⊥       = Nf₊ ⊥ .localize ∘' 𝒥'-map (⊥'-elim {Nf' ⊥})
reify (a ∨ b) = Nf₊ (a ∨ b) .localize ∘' 𝒥'-map [ ∨-I1' ∘' reify a  , ∨-I2' ∘' reify b ]'
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
reflect (◇ a)   = ◇'-map (reflect a) ∘' ◇'-register

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

completeness : Γ ⊨ₐ a → Γ ⊢ a
completeness f = embNf (quot (f ℛ (Nf₊ ∘ 𝕡)))

