module MLPi where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)

-- We do not need separate definitions of values and value types

data 𝕓 : Set where
  𝟙 : 𝕓
  _×_ _+_ : 𝕓 → 𝕓 → 𝕓

data 𝕔 : Set where
  _↔_ : 𝕓 → 𝕓 → 𝕔
  _↝_ : 𝕓 → 𝕓 → 𝕔

-- Defining values and their types together

data val : 𝕓 → Set where
  [] : val 𝟙
  [_,_] : ∀{b₁ b₂}
        → val b₁
        → val b₂
       -----------
        → val (b₁ × b₂)
  left : ∀{b₁ b₂}
        → val b₁
       -----------
        → val (b₁ + b₂)
  right : ∀{b₁ b₂}
        → val b₂
       -----------
        → val (b₁ + b₂)

-- Defining combinators along with types
data comb : 𝕔 → Set where
  swap⁺ : ∀{b₁ b₂ : 𝕓} → comb ((b₁ + b₂) ↔ (b₂ + b₁))
  swapˣ : ∀{b₁ b₂} → comb ((b₁ × b₂) ↔ (b₂ × b₁))
  assocl⁺ : ∀{b₁ b₂ b₃} → comb ((b₁ + (b₂ + b₃)) ↔ ((b₁ + b₂) + b₃))
  assocr⁺ : ∀{b₁ b₂ b₃} → comb (((b₁ + b₂) + b₃) ↔ (b₁ + (b₂ + b₃)))
  assoclˣ : ∀{b₁ b₂ b₃} → comb ((b₁ × (b₂ × b₃)) ↔ ((b₁ × b₂) × b₃))
  assocrˣ : ∀{b₁ b₂ b₃} → comb (((b₁ × b₂) × b₃) ↔ (b₁ × (b₂ × b₃)))
  unite : ∀{b} → comb ((𝟙 × b) ↔ b)
  uniti : ∀{b} → comb (b ↔ (𝟙 × b))
  distrib : ∀{b₁ b₂ b₃} → comb (((b₁ + b₂) × b₃) ↔ ((b₁ × b₃) + (b₂ × b₃)))
  factor : ∀{b₁ b₂ b₃} → comb (((b₁ × b₃) + (b₂ × b₃)) ↔ ((b₁ + b₂) × b₃))
  id : ∀{b} → comb (b ↔ b)
  _+_ : ∀{b₁ b₂ b₃ b₄}
        → comb (b₁ ↔ b₂)
        → comb (b₃ ↔ b₄)
        ----------------
        → comb ((b₁ + b₃) ↔ (b₂ + b₄))
  _×_ : ∀{b₁ b₂ b₃ b₄}
        → comb (b₁ ↔ b₂)
        → comb (b₃ ↔ b₄)
        ----------------
        → comb ((b₁ × b₃) ↔ (b₂ × b₄))
  _!_ : ∀{b₁ b₂ b₃}
        → comb (b₁ ↔ b₂)
        → comb (b₂ ↔ b₃)
        ----------------
        → comb (b₁ ↔ b₃)
  arr : ∀{b₁ b₂}
        → comb (b₁ ↔ b₂)
        ----------------
        → comb (b₁ ↝ b₂)
  _⋙_ : ∀{b₁ b₂ b₃}
        → comb (b₁ ↝ b₂)
        → comb (b₂ ↝ b₃)
        ----------------
        → comb (b₁ ↝ b₃)
  _⊕_ : ∀{b₁ b₂ b₃ b₄}
        → comb (b₁ ↝ b₂)
        → comb (b₃ ↝ b₄)
        ----------------
        → comb ((b₁ + b₃) ↝ (b₂ + b₄))
  _⊗_ : ∀{b₁ b₂ b₃ b₄}
        → comb (b₁ ↝ b₂)
        → comb (b₃ ↝ b₄)
        ----------------
        → comb ((b₁ × b₃) ↝ (b₂ × b₄))
  first : ∀{b₁ b₂ b₃}
        → comb (b₁ ↝ b₂)
        ----------------
        → comb ((b₁ × b₃) ↝ (b₂ × b₃))
  left : ∀{b₁ b₂ b₃}
        → comb (b₁ ↝ b₂)
        ----------------
        → comb ((b₁ + b₃) ↝ (b₂ + b₃))
  create_ : (b : 𝕓)
           ----------------
           → comb (𝟙 ↝ b)
  erase : ∀{b}
           ----------------
           → comb (b ↝ 𝟙)


-- OPERATIONAL SEMANTICS - SEPARATE FOR ARROW CONSTRUCTS

_[_]ᶠ : ∀ {b b'} → comb (b ↔ b') → val b → val b'

swap⁺ [ left v ]ᶠ = right v
swap⁺ [ right v ]ᶠ = left v
swapˣ [ ([ v₁ , v₂ ]) ]ᶠ = [ v₂ , v₁ ]
assocl⁺ [ left v₁ ]ᶠ = left (left v₁)
assocl⁺ [ right (left v₂) ]ᶠ = left (right v₂)
assocl⁺ [ right (right v₃) ]ᶠ = right v₃
assocr⁺ [ left (left v₁) ]ᶠ = left v₁
assocr⁺ [ left (right v₂) ]ᶠ = right (left v₂)
assocr⁺ [ right v₃ ]ᶠ = right (right v₃)
unite [ ([ [] , v ]) ]ᶠ = v
uniti [ v ]ᶠ = [ [] , v ]
assoclˣ [ ([ v₁ , [ v₂ , v₃ ] ]) ]ᶠ = [ [ v₁ , v₂ ] , v₃ ]
assocrˣ [ ([ [ v₁ , v₂ ] , v₃ ]) ]ᶠ = [ v₁ , [ v₂ , v₃ ] ]
distrib [ ([ left v₁ , v₃ ]) ]ᶠ = left ([ v₁ , v₃ ])
distrib [ ([ right v₂ , v₃ ]) ]ᶠ = right ([ v₂ , v₃ ])
factor [ left ([ v₁ , v₃ ]) ]ᶠ = [ left v₁ , v₃ ]
factor [ right ([ v₂ , v₃ ]) ]ᶠ = [ right v₂ , v₃ ]
id [ v ]ᶠ = v
(c₁ + c₂) [ left v₁ ]ᶠ = left (c₁ [ v₁ ]ᶠ)
(c₁ + c₂) [ right v₂ ]ᶠ = right (c₂ [ v₂ ]ᶠ)
(c₁ × c₂) [ ([ v₁ , v₂ ]) ]ᶠ = [ (c₁ [ v₁ ]ᶠ) , (c₂ [ v₂ ]ᶠ) ]
(c₁ ! c₂) [ v ]ᶠ = c₂ [ (c₁ [ v ]ᶠ) ]ᶠ

-- Defining φ which will return a default value of a certain type

φ : (b : 𝕓) → val b
φ 𝟙 = []
φ (b₁ × b₂) = [ φ b₁ , φ b₂ ]
φ (b₁ + b₂) = left (φ b₁)

-- Operational semantics for arrow combinators

_[_]ᵃ : ∀ {b b'} → comb (b ↝ b') → val b → val b'
(arr c) [ v ]ᵃ = c [ v ]ᶠ
(a₁ ⋙ a₂) [ v ]ᵃ = a₂ [ a₁ [ v ]ᵃ ]ᵃ
(a₁ ⊕ a₂) [ left v₁ ]ᵃ = left (a₁ [ v₁ ]ᵃ)
(a₁ ⊕ a₂) [ right v₂ ]ᵃ = right (a₂ [ v₂ ]ᵃ)
(a₁ ⊗ a₂) [ ([ v₁ , v₂ ]) ]ᵃ = [ (a₁ [ v₁ ]ᵃ) , (a₂ [ v₂ ]ᵃ) ]
(left a) [ left v ]ᵃ = left (a [ v ]ᵃ)
(left a) [ right v ]ᵃ = right v
(first a) [ [ v₁ , v₂ ] ]ᵃ = [ (a [ v₁ ]ᵃ) , v₂ ]
erase [ v ]ᵃ = []
(create b) [ [] ]ᵃ = φ b

-----------------------------------  EXAMPLES OF COMBINATORS ------------------------------------------------------

-- 1.FST A

fstA : ∀{b₁ b₂} → comb ((b₁ × b₂) ↝ b₁)
fstA = (((arr swapˣ) ⋙ (first erase)) ⋙ (arr swapˣ)) ⋙ (arr (swapˣ ! unite))

--Proving that it really does erase the 2nd component
fstA-proof : ∀{b₁ b₂} → ∀{v₁ : val b₁} → ∀{v₂ : val b₂} → fstA [ [ v₁ , v₂ ] ]ᵃ ≡ v₁
fstA-proof = refl

-- 2.SND A

sndA : ∀{b₁ b₂} → comb ((b₁ × b₂) ↝ b₂)
sndA = (first erase) ⋙ (arr unite)

--Proving that it really does erase the 2nd component
sndA-proof : ∀{b₁ b₂} → ∀{v₁ : val b₁} → ∀{v₂ : val b₂} → sndA [ [ v₁ , v₂ ] ]ᵃ ≡ v₂
sndA-proof = refl

-- 3.leftA - injecting values in a larger type

leftSwap : ∀{b₁ b₂} → comb (((b₁ + b₂) × b₁) ↔ ((b₁ + b₂) × b₁))
leftSwap = distrib ! ((swapˣ + id) ! factor)

-- For leftA, only really need b₂ in some occasions
leftA : ∀{b₁ b₂} → comb (b₁ ↝ (b₁ + b₂))
leftA {b₁} {b₂} = (((arr uniti) ⋙ (first (create (b₁ + b₂)))) ⋙ (arr leftSwap)) ⋙ fstA

-- Proof that leftA works
leftA-proof : ∀{b₁ b₂} → ∀{v : val b₁} → (leftA {b₁} {b₂}) [ v ]ᵃ ≡ left v
leftA-proof = refl

-- 4.rightA - analogous to leftA

rightSwap : ∀{b₁ b₂} → comb (((b₁ + b₂) × b₂) ↔ ((b₁ + b₂) × b₂))
rightSwap = distrib ! ((id + swapˣ) ! factor)

rightA : ∀{b₁ b₂} → comb (b₂ ↝ (b₁ + b₂))
rightA {b₁} {b₂} = (((arr uniti) ⋙ (first (create (b₂ + b₁)))) ⋙ ((first (arr swap⁺)) ⋙ (arr rightSwap))) ⋙ fstA

rightA-proof : ∀{b₁ b₂} → ∀{v : val b₂} → (rightA {b₁} {b₂}) [ v ]ᵃ ≡ right v
rightA-proof = refl

-- 5.join - forgetting about choices
join : ∀{b} → comb ((b + b) ↝ b)
join = (((arr uniti) ⊕ (arr uniti)) ⋙ (arr factor)) ⋙ sndA

join-proof-left : ∀{b} → ∀{v : val b} → join [ left v ]ᵃ ≡ v
join-proof-left = refl

join-proof-right : ∀{b} → ∀{v : val b} → join [ right v ]ᵃ ≡ v
join-proof-right = refl

-- 6.shuffle - required to clone pairs
shuffle : ∀{b₁ b₂ b₃ b₄} → comb (((b₁ × b₂) × (b₃ × b₄)) ↔ ((b₁ × b₃) × (b₂ × b₄)))
shuffle = assocrˣ ! ((id × (assoclˣ ! ((swapˣ × id) ! assocrˣ))) ! assoclˣ)

shuffle-proof : ∀{b₁ b₂ b₃ b₄} → ∀{v₁ : val b₁} → ∀{v₂ : val b₂} → ∀{v₃ : val b₃} → ∀{v₄ : val b₄} → shuffle [ [ [ v₁ , v₂ ] , [ v₃ , v₄ ] ] ]ᶠ ≡ [ [ v₁ , v₃ ] , [ v₂ , v₄ ] ]
shuffle-proof = refl

-- LEMMA 7.2 CLONING
-- First we will construct a cloning combinator for every type b and then prove its correctness

clone : ∀(b : 𝕓) → (comb (b ↝ (b × b)))
clone 𝟙 = arr uniti
clone (b₁ × b₂) = ((clone b₁) ⊗ (clone b₂)) ⋙ (arr shuffle)
clone (b₁ + b₂) = (((clone b₁) ⋙ ((arr id) ⊗ leftA)) ⊕ ((clone b₂) ⋙ ((arr id) ⊗ rightA))) ⋙ (arr factor)

clone-proof : ∀{b} → ∀(v : val b) → (clone b) [ v ]ᵃ ≡ [ v , v ]
clone-proof [] = refl
clone-proof [ v₁ , v₂ ] rewrite (clone-proof v₁) | (clone-proof v₂) = refl
clone-proof (left v) rewrite (clone-proof v) = refl
clone-proof (right v) rewrite (clone-proof v) = refl

