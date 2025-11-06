{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame

module USet.Base
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (𝕎   : Preorder W _⊆_)
  (let open Preorder 𝕎)
  where

open import Function using (id ; const ; _∘_)

open import Data.Unit
open import Data.Product
  using (Σ; ∃; _×_; _,_; -,_ ; proj₁ ; proj₂ ; uncurry)
open import Data.Empty
open import Data.Sum

private
  variable
    w w' w'' u u' v v' : W

-- Upper set
record USet : Set₁ where
  constructor uset
  field
    Fam : W → Set
    wk  : w ⊆ w' → Fam w → Fam w'

⊤' : USet
⊤' = uset (const ⊤) _

⊥' : USet
⊥' = uset (const ⊥) (const ⊥-elim)

_×'_ : USet → USet → USet
(uset X wkX) ×' (uset Y wkY) = uset (λ w → X w × Y w) wk×
  where
  wk× : w ⊆ w' → X w × Y w → X w' × Y w'
  wk× i (x , y) = (wkX i x) , (wkY i y)

_⊎'_ : USet → USet → USet
(uset X wkX) ⊎' (uset Y wkY) = uset (λ w → X w ⊎ Y w) wk+
  where
  wk+ : w ⊆ w' → X w ⊎ Y w → X w' ⊎ Y w'
  wk+ i (inj₁ x) = inj₁ (wkX i x)
  wk+ i (inj₂ y) = inj₂ (wkY i y)

_→'_ : USet → USet → USet
(uset X wkX) →' (uset Y wkY) = uset (λ w → ∀ {w'} → w ⊆ w' → X w' → Y w') wk→
  where
  wk→ : {w w' : W} → w ⊆ w'
    → ({w1 : W} → w ⊆ w1 → X w1 → Y w1)
    → {w2 : W} → w' ⊆ w2 → X w2 → Y w2
  wk→ i f = λ i' x → f (⊆-trans i i') x

open USet renaming (Fam to _₀_) public

record _→̇_ (X Y : USet) : Set where
  constructor fun
  field
    apply : ∀ {w} → X ₀ w → Y ₀ w

open _→̇_ public

id' : {A : USet} → A →̇ A
id' .apply = id

_∘'_ : {A B C : USet} → B →̇ C → A →̇ B → A →̇ C
(f ∘' g) .apply = f .apply ∘ g .apply

unit' : {A : USet} → A →̇ ⊤'
unit' .apply _ = tt

⟨_,_⟩' : {G A B : USet} → (G →̇ A) → (G →̇ B) → (G →̇ (A ×' B))
⟨ t , u ⟩' = fun λ g → t .apply g , u .apply g

proj₁' : {A B : USet} → (A ×' B) →̇ A
proj₁' .apply = proj₁

proj₂' : {A B : USet} → (A ×' B) →̇ B
proj₂' .apply = proj₂

lam' : {G A B : USet} → ((G ×' A) →̇ B) → G →̇ (A →' B)
lam' {G = G} f .apply g i a = f .apply ((wk G i g) , a)

app' : {G A B : USet} → G →̇ (A →' B) → G →̇ A → G →̇ B
app' t u .apply g = t .apply g ⊆-refl (u .apply g)

eval' : {A B : USet} → ((A →' B) ×' A) →̇ B
eval' = app' proj₁' proj₂'

inj₁' : {A B : USet} → A →̇ (A ⊎' B)
inj₁' .apply = inj₁

inj₂' : {A B : USet} → B →̇ (A ⊎' B)
inj₂' .apply = inj₂

[_,_]' : {A B C : USet} → A →̇ C → B →̇ C → (A ⊎' B) →̇ C
[ f , g ]' .apply = [ f .apply , g .apply ]

curry' : {G A B : USet} → (G ×' A) →̇ B → G →̇ (A →' B)
curry' {G = G} f .apply g i a = f .apply (wk G i g , a)

uncurry' : {G A B : USet} → G →̇ (A →' B) → (G ×' A) →̇ B
uncurry' f .apply (g , x) = f .apply g ⊆-refl x

x-right-assoc : {A B C : USet} → ((A ×' B) ×' C) →̇ (A ×' (B ×' C))
x-right-assoc .apply ((a , b) , c) = a , (b , c)

×'-swap : {A B : USet} → (A ×' B) →̇ (B ×' A)
×'-swap = ⟨ proj₂' , proj₁' ⟩'

_×'-map_ : {A B C D : USet} → A →̇ C → B →̇ D → (A ×' B) →̇ (C ×' D)
f ×'-map g = ⟨ f ∘' proj₁' , g ∘' proj₂' ⟩'

×'-distr-⊎'-forth : {A B C : USet} → (A ×' (B ⊎' C)) →̇ ((A ×' B) ⊎' (A ×' C))
×'-distr-⊎'-forth .apply (a , inj₁ b) = inj₁ (a , b)
×'-distr-⊎'-forth .apply (a , inj₂ c) = inj₂ (a , c)

×'-distr-⊎'-back : {A B C : USet} → ((A ×' B) ⊎' (A ×' C)) →̇ (A ×' (B ⊎' C))
×'-distr-⊎'-back .apply (inj₁ (a , b)) = a , inj₁ b
×'-distr-⊎'-back .apply (inj₂ (a , c)) = a , inj₂ c

⊥'-elim : {A : USet} → ⊥' →̇ A
⊥'-elim .apply = ⊥-elim
