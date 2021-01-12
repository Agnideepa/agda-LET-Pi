module Languages.MLPi where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)
open import Languages.PiTyped using (𝕓 ; _+_ ; _×_ ; 𝟙 ; val ; [] ; [_,_] ; left ; right ; comb₀ ; 𝕔 ; _↔_ ; _[_]ᶠ ;
                                     swap⁺ ; swapˣ ; assoclˣ ; assocrˣ ; unite ; uniti ; distrib ; factor ; id ; _!_)

data ML𝕔 : Set where
  _↝_ : 𝕓 → 𝕓 → ML𝕔

-- Defining combinators along with types
data comb : ML𝕔 → Set where
  arr : ∀{b₁ b₂}
        → comb₀ (b₁ ↔ b₂)
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


-- OPERATIONAL SEMANTICS

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

leftSwap : ∀{b₁ b₂} → comb₀ (((b₁ + b₂) × b₁) ↔ ((b₁ + b₂) × b₁))
leftSwap = distrib ! ((swapˣ + id) ! factor)

-- For leftA, only really need b₂ in some occasions
leftA : ∀{b₁ b₂} → comb (b₁ ↝ (b₁ + b₂))
leftA {b₁} {b₂} = (((arr uniti) ⋙ (first (create (b₁ + b₂)))) ⋙ (arr leftSwap)) ⋙ fstA

-- Proof that leftA works
leftA-proof : ∀{b₁ b₂} → ∀{v : val b₁} → (leftA {b₁} {b₂}) [ v ]ᵃ ≡ left v
leftA-proof = refl

-- 4.rightA - analogous to leftA

rightSwap : ∀{b₁ b₂} → comb₀ (((b₁ + b₂) × b₂) ↔ ((b₁ + b₂) × b₂))
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
shuffle : ∀{b₁ b₂ b₃ b₄} → comb₀ (((b₁ × b₂) × (b₃ × b₄)) ↔ ((b₁ × b₃) × (b₂ × b₄)))
shuffle = assocrˣ ! ((id × (assoclˣ ! ((swapˣ × id) ! assocrˣ))) ! assoclˣ)

shuffle-proof : ∀{b₁ b₂ b₃ b₄} → ∀{v₁ : val b₁} → ∀{v₂ : val b₂} → ∀{v₃ : val b₃} → ∀{v₄ : val b₄} → shuffle [ [ [ v₁ , v₂ ] , [ v₃ , v₄ ] ] ]ᶠ ≡ [ [ v₁ , v₃ ] , [ v₂ , v₄ ] ]
shuffle-proof = refl

-- 7.second
second : ∀{b₁ b₂ b₃} → comb (b₁ ↝ b₂) → comb ((b₃ × b₁) ↝ (b₃ × b₂))
second a = (arr swapˣ) ⋙ ((first a) ⋙ (arr swapˣ))

second-proof : ∀{b₁ b₂ b₃} → ∀{v₁ : val b₃} → ∀{v₂ : val b₁} → ∀{a : comb (b₁ ↝ b₂)} → (second a) [ [ v₁ , v₂ ] ]ᵃ ≡ [ v₁ , a [ v₂ ]ᵃ ]
second-proof = refl

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

