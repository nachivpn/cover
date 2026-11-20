-- Work-in-progress
--{-# OPTIONS --safe --without-K #-}

module Instances.LatLog.STPC.Moderate.Completeness where

open import Instances.LatLog.STPC.Calculus

open import Instances.LatLog.Semantics.Entailment
import Instances.LatLog.Semantics.Interpretation as Interpretation
import Instances.LatLog.Semantics.Soundness as Soundness

open import Function using (_∘_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Product
  using (Σ ; ∃ ; ∃₂ ; _,_ ; -,_ ; proj₁ ; proj₂ ; uncurry) renaming (_×_  to  _×′_) 
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans
  ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst)


-----------------------
-- Base cover system --
-----------------------

data K₊ : Ctx → Set where
  leaf    : (Γ : Ctx) → K₊ Γ
  dead    : Γ ⊢ 𝟘 → K₊ Γ
  branch  : Γ ⊢ (a ＋ b) → K₊ ([] `, a) → K₊ ([] `, b) → K₊ Γ

data _∈₊_ : Ctx → {Γ : Ctx} → K₊ Γ → Set where
  here : Δ ∈₊ leaf Δ
  left : {n : Γ ⊢ (a ＋ b)} {k : K₊ ([] `, a)} {k' : K₊ ([] `, b)}
    → Δ ∈₊ k → Δ ∈₊ branch n k k'
  right : {n : Γ ⊢ (a ＋ b)} {k : K₊ ([] `, a)} {k' : K₊ ([] `, b)}
    → Δ ∈₊ k' → Δ ∈₊ branch n k k'

open import Neighborhood.Lib 𝕎 K₊ _∈₊_
    renaming (∣_∣ to ∣_∣₊ ; ForAllW to ForAllW₊) hiding (Sub)
open import Neighborhood.Systems 𝕎

wkK₊ : Γ ⊑ Γ' → K₊ Γ → K₊ Γ'
wkK₊ i (leaf Δ)        = leaf _
wkK₊ i (dead n)        = dead (wkTm i n)
wkK₊ i (branch n k k') = branch (wkTm i n) k k'

wkK₊-ref : (i : Γ ⊑ Γ') (k : K₊ Γ) → ∣ k ∣₊ ≼ ∣ wkK₊ i k ∣₊
wkK₊-ref i (leaf _) here
    = _ , here , i
wkK₊-ref i (dead x) ()
wkK₊-ref i (branch x k1 k2) (left p)
  = (-, left p , ⊑-refl)
wkK₊-ref i (branch x k1 k2) (right p)
  = (-, right p , ⊑-refl)

idK₊ = leaf

idK₊-sub : ∣ idK₊ Γ ∣₊ ⊆ ⟨ Γ ⟩
idK₊-sub here = ≡-refl

transK₊ : (k : K₊ Γ) → ForAllW₊ k K₊ → K₊ Γ
transK₊ (leaf _)        f = f here
transK₊ (dead x)        f = dead x
transK₊ (branch x k k') f = branch x (transK₊ k (f ∘ left)) (transK₊ k' (f ∘ right))

transK₊-sub : (k : K₊ Γ) (h : ForAllW₊ k K₊)
    → ∣ transK₊ k h ∣₊ ⊆ ⨆ ∣ k ∣₊ (∣_∣₊ ∘ h)
transK₊-sub (leaf Γ)        h p
    = (Γ , here) , p
transK₊-sub (dead x)        h ()
transK₊-sub (branch x k k') h (left p)  =
  let (vl , p') , pl = transK₊-sub k (h ∘ left) p
  in (vl , left p') , pl
transK₊-sub (branch x k k') h (right p) =
  let (vl , p') , pr = transK₊-sub k' (h ∘ right) p
  in (vl , right p') , pr

NS : NeighborhoodSystem
NS = record
  { N = K₊ ; _∈_ = _∈₊_
  ; refinement = record { wkN = wkK₊ ; wkN-ref = wkK₊-ref }
  }

LS : LatLogSystem NS
LS = record
  { identity = record
    { idN[_]  = idK₊
    ; idN-sub = idK₊-sub
    }
  ; transitivity = record
    { transN = transK₊
    ; transN-sub = transK₊-sub
    }
  }

open import USet.Base 𝕎
open import USet.Lattice.Localized 𝕎 LS renaming (LUSetBL to ℛ)

------------------------
-- Model construction --
------------------------

Tm' : Ty → USet
Tm' a = uset (_⊢ a) wkTm

inl' : Tm' a →̇ Tm' (a ＋ b)
inl' .apply = inl

inr' : Tm' b →̇ Tm' (a ＋ b)
inr' .apply = inr

localizeTm : (k : K₊ Γ) → ForAllW₊ k (_⊢ a) → Γ ⊢ a
localizeTm (leaf x)         h = h here
localizeTm (dead x)         h = abort x
localizeTm (branch x k1 k2) h = match x (localizeTm k1 (h ∘ left)) (localizeTm k2 (h ∘ right))
  
Tm₊ : Ty → LUSet
Tm₊ a = luset (Tm' a) (run𝒥' {Tm' a} localizeTm)

open Interpretation ℛ (Tm₊ ∘ 𝕡) using (⟦_⟧ ; ⟦_⟧c)-- imports ⟦-⟧
open LUSet -- imports localize and 𝒳

---------------------
-- Residualization --
---------------------

--reify   : ∀ a → ⟦ a ⟧ →̇₊ (Tm₊ a)
-- or equivalently:
reify   : ∀ a → ⟦ a ⟧ .𝒳 →̇ Tm' a
reflect : ∀ a → Tm' a →̇ ⟦ a ⟧ .𝒳

reify (𝕡 i)   = id'
reify 𝟙       = fun (λ _ → unit)
reify (a × b) = fun λ x → pair (reify a .apply (proj₁ x)) (reify b .apply (proj₂ x))
reify 𝟘       = Tm₊ 𝟘 .localize ∘' map𝒥' (⊥'-elim {Tm' 𝟘})
reify (a ＋ b) = Tm₊ (a ＋ b) .localize ∘' map𝒥' [ inl' ∘' reify a  , inr' ∘' reify b ]'

reflect (𝕡 i)   = id'
reflect 𝟙       = unit'
reflect (a × b) = fun λ n → reflect a .apply (fst n) , reflect b .apply (snd n)
reflect 𝟘       = fun λ n → dead n , λ {()}
reflect (a ＋ b) = fun λ n → branch n (leaf (_ `, a)) (leaf (_ `, b)) ,
  λ { (left here)  → inj₁ (reflect a .apply (var zero))
    ; (right here) → inj₂ (reflect b .apply (var zero))
    }

------------------
-- Completeness --
------------------

idEnv : ∀ Γ → ⟦ Γ ⟧c .𝒳 ₀ Γ
idEnv []       = _
idEnv (Γ `, a) = wk (⟦ Γ ⟧c .𝒳) freshWk (idEnv Γ) , reflect a .apply (var zero)

quot : (⟦ Γ ⟧c →̇₊ ⟦ a ⟧) → Γ ⊢ a
quot {Γ} {a} f = reify a .apply (f .apply (idEnv Γ))

completeness : Γ ⊨ₐ a → Γ ⊢ a
completeness f = quot (f ℛ (Tm₊ ∘ 𝕡))

open Soundness.Proof ℛ (Tm₊ ∘ 𝕡) hiding ([_,_]')

eval : Γ ⊢ a → ⟦ Γ ⟧c →̇₊ ⟦ a ⟧
eval t = ⟦-⟧-sound t

norm : Γ ⊢ a → Γ ⊢ a
norm t = quot (eval t)

-----------------------
-- Correctness (WIP) --
-----------------------

open import Instances.LatLog.STPC.Moderate.Conversion

yoga : (a : Ty) → (n : Γ ⊢ a)
  → n ≈ reify a .apply (reflect a .apply n)
yoga (𝕡 x) n   = ≈-refl
yoga 𝟙 n       = exp-𝟙 n
yoga 𝟘 n       = exp-𝟘 n
yoga (a × b) n = ≈-trans
  (exp-× n)
  (con-pair (yoga a (fst n)) (yoga b (snd n)))
yoga (a ＋ b) n = ≈-trans
  (exp-＋ n)
  (con-match ≈-refl (con-inl (yoga a (var zero)))
  (con-inr (yoga b (var zero))))

Val₊- : Ty → LUSet
Val₊- = ⟦_⟧

Val'- : Ty → USet
Val'- a = Val₊- a .𝒳

Val' : Ctx → Ty → Set
Val' Γ a = Val'- a ₀ Γ

wkVal' : (w : Γ ⊑ Γ') → Val' Γ a → Val' Γ' a
wkVal' {a = a} w t = wk (⟦ a ⟧ .𝒳) w t

Env'- : Ctx → USet
Env'- a = ⟦ a ⟧c .𝒳

Env' : Ctx → Ctx → Set
Env' Γ a = Env'- a ₀ Γ

wkEnv' : (w : Γ ⊑ Γ') → Env' Γ Δ → Env' Γ' Δ
wkEnv' {Γ} {Γ'} {Δ} w s = wk (⟦ Δ ⟧c .𝒳) w s

open import Data.Unit renaming (⊤ to ⊤′)
open import Data.Sum 

module _ (X : USet) where
  ℒᴷ : (Rl : ∀ {Δ} → Tm Δ a → X ₀ Δ → Set)
    → Tm Γ a → (k : K₊ Γ) → ForAllW₊ k (X ₀_) → Set
  ℒᴷ Rl t (leaf Γ) f         = Rl t (f here) 
  ℒᴷ Rl t (dead x) _         = t ≈ abort x
  ℒᴷ Rl t (branch x k₁ k₂) f = ∃₂ λ t₁ t₂
    →  ℒᴷ Rl t₁ k₁ (f ∘ left)
    ×′ ℒᴷ Rl t₂ k₂ (f ∘ right)
    ×′ t ≈ match x t₁ t₂

mutual
  ℒ₊ : Tm Γ (a ＋ b) → (Val' Γ a) ⊎ (Val' Γ b) → Set  
  ℒ₊ t (inj₁ x) = ∃ λ t' → ℒ _ t' x ×′ t ≈ inl t'
  ℒ₊ t (inj₂ y) = ∃ λ t' → ℒ _ t' y ×′ t ≈ inr t'

  ℒ₀ : Tm Γ 𝟘 → ⊥' ₀ Γ → Set  
  ℒ₀ t ()
  
  ℒ : (a : Ty) → (t : Tm Γ a) → (x : Val' Γ a) → Set
  ℒ (𝕡 ι)   t x       = t ≈ x
  ℒ 𝟙       t x       = ⊤′
  ℒ 𝟘       t (k , f) = ℒᴷ ⊥' ℒ₀ t k f
  ℒ (a × b) t (x , y) = ℒ a (fst t) x ×′ ℒ b (snd t) y
  ℒ (a ＋ b) t (k , f) = ℒᴷ (Val'- a ⊎' Val'- b) ℒ₊ t k f

ℒˢ : {Γ : Ctx} (Δ : Ctx) → Sub Γ Δ → Env' Γ Δ → Set
ℒˢ []       []       tt      = ⊤′
ℒˢ (Δ `, a) (s `, t) (δ , x) = ℒˢ Δ s δ ×′ ℒ a t x

-- switching to families of sets should get rid of the these
-- the "clever" choice to instantiate upsets with
-- the identity relation has bitten me back
postulate
  wkTm-pres-id : ∀ (t : Tm Γ a) → wkTm ⊑-refl t ≡ t
  wkTm-pres-ℒ : {t : Tm Γ a} {x : Val' Γ a}
    → (w : Γ ⊑ Γ')
    → (tLx : ℒ a t x)
    → ℒ a (wkTm w t) (wkVal' {a = a} w x)
    
ℒᴷ₊-prepend : {t u : Tm Γ (a ＋ b)} (k : K₊ Γ) (f : ForAllW₊ k ((Val'- a ⊎' Val'- b) ₀_))
      → t ≈ u
      → ℒᴷ (Val'- a ⊎' Val'- b) ℒ₊ u k f
      → ℒᴷ (Val'- a ⊎' Val'- b) ℒ₊ t k f
ℒᴷ₊-prepend (leaf Γ) f t≈u p with f here | p 
... | inj₁ x | t' , p , u≈inlt' = t' , p , ≈-trans t≈u u≈inlt'
... | inj₂ y | t' , p , u≈inrt' = t' , p , ≈-trans t≈u u≈inrt'
ℒᴷ₊-prepend (dead x) f t≈u u≈abx
  = ≈-trans t≈u u≈abx
ℒᴷ₊-prepend (branch x k k₁) f t≈u (t₁ , t₂ , q₁ , q₂ , u≈matchxt₁t₂)
  = t₁ , t₂ , q₁ , q₂ , ≈-trans t≈u u≈matchxt₁t₂

ℒᴷ₀-prepend : {t u : Tm Γ 𝟘} (k : K₊ Γ) (f : ForAllW₊ k (⊥' ₀_))
      → t ≈ u
      → ℒᴷ ⊥' ℒ₀ u k f
      → ℒᴷ ⊥' ℒ₀ t k f
ℒᴷ₀-prepend (leaf Γ)        f t≈u p with f here
... | () 
ℒᴷ₀-prepend (dead x)        f t≈u p
  = ≈-trans t≈u p
ℒᴷ₀-prepend (branch x k₁ k₂) f t≈u (t₁ , t₂ , q₁ , q₂ , u≈matchxt₁t₂)
  = t₁ , t₂ , q₁ , q₂ , ≈-trans t≈u u≈matchxt₁t₂

ℒ-prepend : (a : Ty) {t u : Tm Γ a} {x : Val' Γ a}
    → t ≈ u → ℒ a u x → ℒ a t x
ℒ-prepend (𝕡 x) t≈u uLx
  = ≈-trans t≈u uLx
ℒ-prepend 𝟙 t≈u uLx
  = tt
ℒ-prepend 𝟘 {x = k , f} t≈u  p
  = ℒᴷ₀-prepend k f t≈u p
ℒ-prepend (a × b) t≈u (uLx , uLy)
  = ℒ-prepend a (con-fst t≈u) uLx , ℒ-prepend b (con-snd t≈u) uLy
ℒ-prepend (a ＋ b) {x = k , f} t≈u  p
  = ℒᴷ₊-prepend k f t≈u p

ℒ-reflect : (a : Ty) (n : Tm Γ a) → ℒ a n (reflect a .apply n)
ℒ-reflect (𝕡 x)    n = ≈-refl
ℒ-reflect 𝟙        n = tt
ℒ-reflect 𝟘        n = exp-𝟘 n
ℒ-reflect (a × b)  n = ℒ-reflect a (fst n) , ℒ-reflect b (snd n)
ℒ-reflect (a ＋ b) n = inl x₀ , inr x₀
  , (x₀ , ℒ-reflect a x₀ , ≈-refl)
  , (x₀ , ℒ-reflect b x₀ , ≈-refl)
  , exp-＋ n

mutual
  ℒᴷ₊-build : {t : Tm Γ (a ＋ b)} (k : K₊ Γ) (f : ForAllW₊ k ((Val'- a ⊎' Val'- b) ₀_))
    → ℒᴷ (Val'- a ⊎' Val'- b) ℒ₊ t k f
    → t ≈ reify (a ＋ b) .apply (k , f)
  ℒᴷ₊-build (leaf Γ) f p with f here | p
  ... | inj₁ x | t' , p , t≈inlt' = ≈-trans t≈inlt' (con-inl (ℒ-build _ p))
  ... | inj₂ y | t' , p , t≈inrt' = ≈-trans t≈inrt' (con-inr (ℒ-build _ p))
  ℒᴷ₊-build (dead x) f p
    = p
  ℒᴷ₊-build (branch x k₁ k₂) f (t₁ , t₂ , q₁ , q₂ , t≈matchxt₁t₂)
    = ≈-trans t≈matchxt₁t₂
        (con-match ≈-refl
          (ℒᴷ₊-build k₁ (f ∘ left) q₁)
          (ℒᴷ₊-build k₂ (f ∘ right) q₂))

  ℒᴷ₀-build : {t : Tm Γ 𝟘} (k : K₊ Γ) (f : ForAllW₊ k (⊥' ₀_))
    → ℒᴷ ⊥' ℒ₀ t k f
    → t ≈ reify 𝟘 .apply (k , f)
  ℒᴷ₀-build (leaf Γ) f p with f here
  ... | ()
  ℒᴷ₀-build (dead x) f p = p
  ℒᴷ₀-build (branch x k₁ k₂) f (t₁ , t₂ , q₁ , q₂ , t≈matchxt₁t₂)
    = ≈-trans t≈matchxt₁t₂
        (con-match ≈-refl
          (ℒᴷ₀-build k₁ (f ∘ left) q₁)
          (ℒᴷ₀-build k₂ (f ∘ right) q₂))
  
  ℒ-build : (a : Ty) → {t : Tm Γ a} {x : Val' Γ a} → ℒ a t x → t ≈ reify a .apply x
  ℒ-build (𝕡 x)   p
    = p
  ℒ-build 𝟙 p
    = exp-𝟙 _
  ℒ-build 𝟘 {x = k , f} p
    = ℒᴷ₀-build k f p
  ℒ-build (a × b) (p , q)
    = ≈-trans (exp-× _) (con-pair (ℒ-build a p) (ℒ-build b q))
  ℒ-build (a ＋ b) {x = k , f} p
    = ℒᴷ₊-build k f p

wkSub-pres-ℒˢ : {s : Sub Γ Δ} {δ : Env' Γ Δ}
    → (w : Γ ⊑ Γ')
    → (sLδ : ℒˢ Δ s δ)
    → ℒˢ Δ (wkSub w s) (wkEnv' {Δ = Δ} w δ)
wkSub-pres-ℒˢ {s = []}       w p
  = tt 
wkSub-pres-ℒˢ {s = _s `, t}  w (sLδ , tLx)
  = wkSub-pres-ℒˢ w sLδ , wkTm-pres-ℒ {t = t} w tLx
    
idℒˢ : ∀ Δ → ℒˢ Δ idˢ (idEnv Δ)
idℒˢ []       = tt
idℒˢ (Δ `, a) = wkSub-pres-ℒˢ freshWk (idℒˢ Δ) , ℒ-reflect a (var zero)
  
Fund : Tm Δ a → Set
Fund {Δ} {a} t = ∀ {Γ} {s : Sub Γ Δ} {δ : Env' Γ Δ}
  → (sLδ : ℒˢ Δ s δ) → ℒ a (substTm s t) (eval t .apply δ)

fund-var : (v : Var Δ a) {s : Sub Γ Δ} {δ : Env' Γ Δ}
  → (sLδ : ℒˢ Δ s δ)
  → ℒ a (substVar s v) (eval (var v) .apply δ)
fund-var v0       {s = _ `, _}  (_ , sLδ) = sLδ
fund-var (succ v) {s = _ `, _} (sLδ  , _tLx) = fund-var v sLδ

fundLocTm : (t : Tm Γ a) (k : K₊ Γ) (f : ForAllW₊ k ((Tm' a) ₀_))
  → ℒᴷ (Tm' a) _≈_ t k f
  → t ≈ localizeTm k f
fundLocTm t (leaf Γ) f p = p
fundLocTm t (dead x) f p = p
fundLocTm t (branch x k k₁) f (t₁ , t₂ , q₁ , q₂ , t≈matchxt₁t₂)
  = ≈-trans t≈matchxt₁t₂ (con-match ≈-refl (fundLocTm t₁ k (f ∘ left) q₁) (fundLocTm t₂ k₁ (f ∘ right) q₂))

fundJoin₀ : (t : Tm Γ 𝟘) (k : K₊ Γ) (f : ForAllW₊ k (𝒥' ⊥' ₀_))
    → ℒᴷ (𝒥' ⊥') (λ u → uncurry (ℒᴷ ⊥' ℒ₀ u)) t k f
    → uncurry (ℒᴷ ⊥' ℒ₀ t) (𝒥'-join {A = ⊥'} .apply (k , f))
fundJoin₀ t (leaf Γ) f p = p
fundJoin₀ t (dead x) f p = p
fundJoin₀ t (branch x k₁ k₂) f (t₁ , t₂ , q₁ , q₂ , t≈matchxt₁t₂)
  = t₁
  , t₂
  , fundJoin₀ t₁ k₁ (f ∘ left) q₁
  , fundJoin₀ t₂ k₂ (f ∘ right) q₂
  , t≈matchxt₁t₂  

-- likely doable, stopped by the requirement for presheaf laws
-- again can be achieved by switching to families
postulate
  fundLoc : (t : Tm Γ a) (k : K₊ Γ) (f : ForAllW₊ k ((Val'- a) ₀_))
    → ℒᴷ (Val'- a) (ℒ a) t k f
    → ℒ a t (localize ⟦ a ⟧ .apply (k , f))
    
fundAbort : (t : Tm Γ 𝟘) (k : K₊ Γ) (f : ForAllW₊ k (⊥' ₀_))
    → ℒ 𝟘 t (k , f)
    → ℒᴷ (Val'- a) (ℒ a) (abort t) k (⊥'-elim {Val'- a} .apply  ∘ f)
fundAbort t (leaf Γ) f p with f here
... | () 
fundAbort t (dead x) f p
  = ≈-trans (con-abort p) per-𝟘-𝟘
fundAbort t (branch x k k₁) f (t₁ , t₂ , q₁ , q₂ , t≈matchxt₁t₂)
  = abort t₁
  , abort t₂
  , fundAbort t₁ k (f ∘ left) q₁
  , (fundAbort t₂ k₁ (f ∘ right) q₂)
  , ≈-trans (con-abort t≈matchxt₁t₂) per-＋-𝟘

fundMatch : (t : Tm Γ (a ＋ b)) (k : K₊ Γ) (f : ForAllW₊ k ((Val'- a ⊎' Val'- b) ₀_))
    (t₁ : Tm ([] `, a) c) (g : Val'- a →̇ Val'- c)
    (t₂ : Tm ([] `, b) c) (h : Val'- b →̇ Val'- c)
    → ℒ (a ＋ b) t (k , f)
    → ({Δ : Ctx} {u : Tm Δ a} {x : Val' Δ a} → ℒ a u x → ℒ c (substTm ([] `, u) t₁) (g .apply x))
    → ({Δ : Ctx} {u : Tm Δ b} {x : Val' Δ b} → ℒ b u x → ℒ c (substTm ([] `, u) t₂) (h .apply x))
    → ℒᴷ (Val'- c) (ℒ c)
         (match t t₁ t₂)
         k ([ g , h ]' .apply  ∘ f)
fundMatch {c = c} t (leaf Γ) f t₁ g t₂ h p q r with f here | p
... | inj₁ x | t' , p , tr = ℒ-prepend c (≈-trans (con-match tr ≈-refl ≈-refl) (red-＋1 t' t₁ t₂)) (q p)
... | inj₂ y | t' , p , tr = ℒ-prepend c (≈-trans (con-match tr ≈-refl ≈-refl) (red-＋2 t' t₁ t₂)) (r p)
fundMatch t (dead x) f t₁ x₁ t₂ x₂ p q r
  = ≈-trans (con-match p ≈-refl ≈-refl) per-𝟘-＋
fundMatch {a = a} {b = b} {c = c} t (branch x k₁ k₂) f t₁ x₁ t₂ x₂ (t₃ , t₄ , p₁ , p₂ , t≈matchxt₃t₄) q r
  = match t₃ t₁ t₂
  , match t₄ t₁ t₂
  , fundMatch t₃ k₁ (f ∘ left) t₁ x₁ t₂ x₂ p₁ q r
  , fundMatch t₄ k₂ (f ∘ right) t₁ x₁ t₂ x₂ p₂ q r
  , ≈-trans (con-match t≈matchxt₃t₄ ≈-refl ≈-refl) per-＋-＋

fund : (t : Tm Δ a) → Fund t
fund (var x) {Γ} {s} {δ} sLδ
  = fund-var x sLδ
fund unit {Γ} {s} {δ} sLδ
  = tt
fund {a = a} (abort t) {Γ} {s} {δ} sLδ
  = let kf@(k , f) = eval t .apply δ
    in fundLoc {Γ = Γ} {a = a} (abort (substTm s t)) _ _
       (fundAbort
         (substTm s t) k f (fund t sLδ))
fund {a = a × b} (pair t u) {Γ} {s} {δ} sLδ 
  = ℒ-prepend a red-×1 (fund t sLδ)
  , ℒ-prepend b red-×2 (fund u sLδ)
fund (fst t) {Γ} {s} {δ} sLδ
  = proj₁ (fund t sLδ)
fund (snd t) {Γ} {s} {δ} sLδ
  = proj₂ (fund t sLδ)
fund (inl t) {Γ} {s} {δ} sLδ
  = wkTm ⊑-refl (substTm s t)
  , wkTm-pres-ℒ {t = substTm s t} ⊑-refl (fund t sLδ)
  , con-inl (≡-to-≈ (≡-sym (wkTm-pres-id (substTm s t))))
fund (inr t) {Γ} {s} {δ} sLδ
  = wkTm ⊑-refl (substTm s t)
  , wkTm-pres-ℒ {t = substTm s t} ⊑-refl (fund t sLδ)
  , con-inr (≡-to-≈ (≡-sym (wkTm-pres-id (substTm s t))))
fund {a = a} (match t t₁ t₂) {Γ} {s} {δ} sLδ
  = let kf@(k , f) = eval t .apply δ
    in fundLoc {Γ = Γ} {a = a} (match (substTm s t) t₁ t₂) _ _
       (fundMatch 
         (substTm s t) k f
         t₁ (fun (λ x → eval t₁ .apply (tt , x)))
         t₂ (fun (λ x → eval t₂ .apply (tt , x)))
         (fund t sLδ)
         (λ z → fund t₁ (tt , z))
         (λ z → fund t₂ (tt , z)))

quotTm-retracts-eval : (t : Tm Γ a) → t ≈ quot (eval t)
quotTm-retracts-eval t = ℒ-build _
  (ℒ-prepend _
    (≡-to-≈ (≡-sym (substTm-pres-idˢ t)))
    (fund t (idℒˢ _)))

-- normalization is sound 
norm-sound : {t u : Tm Γ a} → norm t ≡ norm u → t ≈ u
norm-sound {Γ} {a} {t} {u} nt≡nu = ≈-trans
    (quotTm-retracts-eval t)
    (≈-trans
      (≡-to-≈ nt≡nu)
      (≈-sym (quotTm-retracts-eval u)))
