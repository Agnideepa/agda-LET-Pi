\begin{code}
module Languages.PiTyped where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)

-- Type universe -- should combinator types be separate from value types?

data 𝕓 : Set where
  𝟙 : 𝕓
  _×_ _+_ : 𝕓 → 𝕓 → 𝕓

data 𝕔 : Set where
  _↔_ : 𝕓 → 𝕓 → 𝕔

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
data comb₀ : 𝕔 → Set where
  swap⁺ : ∀{b₁ b₂ : 𝕓} → comb₀ ((b₁ + b₂) ↔ (b₂ + b₁))
  swapˣ : ∀{b₁ b₂} → comb₀ ((b₁ × b₂) ↔ (b₂ × b₁))
  assocl⁺ : ∀{b₁ b₂ b₃} → comb₀ ((b₁ + (b₂ + b₃)) ↔ ((b₁ + b₂) + b₃))
  assocr⁺ : ∀{b₁ b₂ b₃} → comb₀ (((b₁ + b₂) + b₃) ↔ (b₁ + (b₂ + b₃)))
  assoclˣ : ∀{b₁ b₂ b₃} → comb₀ ((b₁ × (b₂ × b₃)) ↔ ((b₁ × b₂) × b₃))
  assocrˣ : ∀{b₁ b₂ b₃} → comb₀ (((b₁ × b₂) × b₃) ↔ (b₁ × (b₂ × b₃)))
  unite : ∀{b} → comb₀ ((𝟙 × b) ↔ b)
  uniti : ∀{b} → comb₀ (b ↔ (𝟙 × b))
  distrib : ∀{b₁ b₂ b₃} → comb₀ (((b₁ + b₂) × b₃) ↔ ((b₁ × b₃) + (b₂ × b₃)))
  factor : ∀{b₁ b₂ b₃} → comb₀ (((b₁ × b₃) + (b₂ × b₃)) ↔ ((b₁ + b₂) × b₃))
  id : ∀{b} → comb₀ (b ↔ b)
  _+_ : ∀{b₁ b₂ b₃ b₄}
        → comb₀ (b₁ ↔ b₂)
        → comb₀ (b₃ ↔ b₄)
        ----------------
        → comb₀ ((b₁ + b₃) ↔ (b₂ + b₄))
  _×_ : ∀{b₁ b₂ b₃ b₄}
        → comb₀ (b₁ ↔ b₂)
        → comb₀ (b₃ ↔ b₄)
        ----------------
        → comb₀ ((b₁ × b₃) ↔ (b₂ × b₄))
  _!_ : ∀{b₁ b₂ b₃}
        → comb₀ (b₁ ↔ b₂)
        → comb₀ (b₂ ↔ b₃)
        ----------------
        → comb₀ (b₁ ↔ b₃)
  symm : ∀{b₁ b₂}
        → comb₀ (b₁ ↔ b₂)
        ----------------
        → comb₀ (b₂ ↔ b₁)
  
  
_† : ∀{b b' : 𝕓} → comb₀ (b ↔ b') → comb₀ (b' ↔ b)
swap⁺ † = swap⁺
assoclˣ † = assocrˣ
assocrˣ † = assoclˣ
assocl⁺ † = assocr⁺
assocr⁺ † = assocl⁺
distrib † = factor
factor † = distrib
unite † = uniti
uniti † = unite
id † = id
swapˣ † = swapˣ
(c₁ + c₂)† = (c₁ †) + (c₂ †)
(c₁ × c₂)† = (c₁ †) × (c₂ †)
(c₁ ! c₂)† = (c₂ †) ! (c₁ †)
(symm c)† = c
  

-- OPERATIONAL SEMANTICS - BOTH BACKWARD AND FORWARD DIRECTIONS --
\end{code}

%<*pi-eval>
\begin{code}
_[_]ᶠ : ∀ {b b'} → comb₀ (b ↔ b') → val b → val b'
_[_]ᵇ : ∀ {b b'} → comb₀ (b ↔ b') → val b' → val b

\end{code}
%</pi-eval>

\begin{code}
swap⁺ [ left v ]ᶠ = right v
swap⁺ [ right v ]ᶠ = left v
swapˣ [ ([ v₁ , v₂ ]) ]ᶠ = [ v₂ , v₁ ]
assocl⁺ [ left v₁ ]ᶠ = left (left v₁)
assocl⁺ [ right (left v₂) ]ᶠ = left (right v₂)
assocl⁺ [ right (right v₃) ]ᶠ = right v₃
assocr⁺ [ left (left v₁) ]ᶠ = left v₁
assocr⁺ [ left (right v₂) ]ᶠ = right (left v₂)
assocr⁺ [ right v₃ ]ᶠ = right (right v₃)
unite [ ([ unit , v ]) ]ᶠ = v
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
(symm c) [ v ]ᶠ = c [ v ]ᵇ

swap⁺ [ left v ]ᵇ = right v
swap⁺ [ right v ]ᵇ = left v
swapˣ [ ([ v₁ , v₂ ]) ]ᵇ = [ v₂ , v₁ ]
assocr⁺ [ left v₁ ]ᵇ = left (left v₁)
assocr⁺ [ right (left v₂) ]ᵇ = left (right v₂)
assocr⁺ [ right (right v₃) ]ᵇ = right v₃
assocl⁺ [ left (left v₁) ]ᵇ = left v₁
assocl⁺ [ left (right v₂) ]ᵇ = right (left v₂)
assocl⁺ [ right v₃ ]ᵇ = right (right v₃)
uniti [ ([ unit , v ]) ]ᵇ = v
unite [ v ]ᵇ = [ [] , v ]
assocrˣ [ ([ v₁ , [ v₂ , v₃ ] ]) ]ᵇ = [ [ v₁ , v₂ ] , v₃ ]
assoclˣ [ ([ [ v₁ , v₂ ] , v₃ ]) ]ᵇ = [ v₁ , [ v₂ , v₃ ] ]
factor [ ([ left v₁ , v₃ ]) ]ᵇ = left ([ v₁ , v₃ ])
factor [ ([ right v₂ , v₃ ]) ]ᵇ = right ([ v₂ , v₃ ])
distrib [ left ([ v₁ , v₃ ]) ]ᵇ = [ left v₁ , v₃ ]
distrib [ right ([ v₂ , v₃ ]) ]ᵇ = [ right v₂ , v₃ ]
id [ v ]ᵇ = v
(c₁ + c₂) [ left v₁ ]ᵇ = left (c₁ [ v₁ ]ᵇ)
(c₁ + c₂) [ right v₂ ]ᵇ = right (c₂ [ v₂ ]ᵇ)
(c₁ × c₂) [ ([ v₁ , v₂ ]) ]ᵇ = [ (c₁ [ v₁ ]ᵇ) , (c₂ [ v₂ ]ᵇ) ]
(c₁ ! c₂) [ v ]ᵇ = c₁ [ (c₂ [ v ]ᵇ) ]ᵇ
(symm c) [ v ]ᵇ = c [ v ]ᶠ


-- Proof of reversibility

-- x₁ = x₂ ^ y₁ = y₂ → [ x₁ , y₁ ] = [ x₂ , y₂ ] - for equality of pairs - not sure if this is necessary
[]-cong : ∀ {b₁ b₂} → ∀ {x₁ x₂ : val b₁} → ∀ {y₁ y₂ : val b₂} →  x₁ ≡ x₂ → y₁ ≡ y₂ → [ x₁ , y₁ ] ≡ [ x₂ , y₂ ]
[]-cong refl refl = refl

--IDEAS THAT DID NOT WORK

{-data _on_↦_ : ∀ {b b'} → comb₀ (b ↔ b') → val b → val b' → Set where
  swap⁺left : ∀{b₁} → ∀ {v : val b₁} → swap⁺ on (left v) ↦ (right v)
  swap⁺right : ∀{b₂} → ∀ {v : val b₂} → swap⁺ on (right v) ↦ (left v)
  _×_ : ∀ {b₁ b₂ b₃ b₄}{v₁ v₂ v₃ v₄} → ∀ {c₁ : comb₀ (b₁ ↔ b₃)} → ∀ {c₂ : comb₀ (b₂ ↔ b₄)}  
       → c₁ on v₁ ↦ v₃
       → c₂ on v₂ ↦ v₄
       --------------
       → (c₁ × c₂) on [ v₁ , v₂ ] ↦ [ v₃ , v₄ ]
-}

-- TO PROVE OTHER SIDE OF THE PROPOSITION

{- First we postulate a form of extensionality for combinators. If they
   lead to the same forward evaluation, then they are equal.
-}

{- postulate
  comb-extensionality : ∀ {b b'} (c₁ c₂ : comb₀ (b ↔ b'))
    → ((v : val b) → (v' : val b') → c₁ [ v ]ᶠ ≡ v' → c₂ [ v ]ᶠ ≡ v' )
    --→ (∀(v v') → c₂ [ v ]ᶠ ≡ v' → c₁ [ v ]ᶠ ≡ v' )
      -----------------------
    → c₁ ≡ c₂
symm=c† : ∀ {b b'} (c : comb₀ (b ↔ b')) → (symm c) ≡ (c †)
symm=c† c = comb-extensionality (symm c) (c †) (λ{v v' pr → lemma-3 c v' (lemma-2 c v pr)})
adj-of-adj-is-id : ∀ {b b'} → ∀ (c : comb₀ (b ↔ b')) → ((c †) †) ≡ c
adj-of-adj-is-id swap⁺ = refl
adj-of-adj-is-id assoclˣ = refl
adj-of-adj-is-id assocrˣ = refl
adj-of-adj-is-id assocl⁺ = refl
adj-of-adj-is-id assocr⁺ = refl
adj-of-adj-is-id distrib = refl
adj-of-adj-is-id factor = refl
adj-of-adj-is-id unite = refl
adj-of-adj-is-id uniti = refl
adj-of-adj-is-id id = refl
adj-of-adj-is-id swapˣ = refl
adj-of-adj-is-id (c₁ + c₂) rewrite adj-of-adj-is-id c₁ | adj-of-adj-is-id c₂ = refl
adj-of-adj-is-id (c₁ × c₂) rewrite adj-of-adj-is-id c₁ | adj-of-adj-is-id c₂ = refl
adj-of-adj-is-id (c₁ ! c₂) rewrite adj-of-adj-is-id c₁ | adj-of-adj-is-id c₂ = refl
adj-of-adj-is-id (symm c) = sym (symm=c† c)
-}

-- FIRST WE PROVE THAT FORWARD AND BACKWARD EVALUATION ARE INVERSES OF EACH OTHER

lemma-1 : ∀ {b b'} → ∀(c : comb₀ (b ↔ b')) → ∀ (v : val b) → c [ c [ v ]ᶠ ]ᵇ ≡ v
lemma-2 : ∀ {b b'} → ∀(c : comb₀ (b ↔ b')) → ∀ (v : val b') → c [ c [ v ]ᵇ ]ᶠ ≡ v

lemma-1 swap⁺ (left v) = refl
lemma-1 swap⁺ (right v) = refl
lemma-1 swapˣ ([ v₁ , v₂ ]) = refl
lemma-1 assocl⁺ (left v₁) = refl
lemma-1 assocl⁺ (right (left v₂)) = refl
lemma-1 assocl⁺ (right (right v₃)) = refl
lemma-1 assocr⁺ (left (left v₁)) = refl
lemma-1 assocr⁺ (left (right v₂)) = refl
lemma-1 assocr⁺ (right v₃) = refl
lemma-1 unite ([ [] , v ]) = refl
lemma-1 uniti v = refl
lemma-1 assoclˣ ([ v₁ , [ v₂ , v₃ ] ]) = refl
lemma-1 assocrˣ ([ [ v₁ , v₂ ] , v₃ ]) = refl
lemma-1 distrib ([ left v₁ , v₃ ]) = refl
lemma-1 distrib ([ right v₂ , v₃ ]) = refl
lemma-1 factor (left ([ v₁ , v₃ ])) = refl
lemma-1 factor (right ([ v₂ , v₃ ])) = refl
lemma-1 id v = refl
lemma-1 (c₁ + c₂) (left v₁) = cong left (lemma-1 c₁ v₁)
lemma-1 (c₁ + c₂) (right v₂) = cong right (lemma-1 c₂ v₂)
lemma-1 (c₁ × c₂) ([ v₁ , v₂ ]) = []-cong (lemma-1 c₁ v₁) (lemma-1 c₂ v₂)
-- REWRITE THIS TO MAKE USE OF LESS CONFUSING SYNTAX
lemma-1 (c₁ ! c₂) v = trans (cong (c₁ [_]ᵇ) (lemma-1 c₂ (c₁ [ v ]ᶠ))) (lemma-1 c₁ v)
lemma-1 (symm c) v = lemma-2 c v

lemma-2 swap⁺ (left v) = refl
lemma-2 swap⁺ (right v) = refl
lemma-2 swapˣ ([ v₁ , v₂ ]) = refl
lemma-2 assocr⁺ (left v₁) = refl
lemma-2 assocr⁺ (right (left v₂)) = refl
lemma-2 assocr⁺ (right (right v₃)) = refl
lemma-2 assocl⁺ (left (left v₁)) = refl
lemma-2 assocl⁺ (left (right v₂)) = refl
lemma-2 assocl⁺ (right v₃) = refl
lemma-2 uniti ([ [] , v ]) = refl
lemma-2 unite v = refl
lemma-2 assocrˣ ([ v₁ , [ v₂ , v₃ ] ]) = refl
lemma-2 assoclˣ ([ [ v₁ , v₂ ] , v₃ ]) = refl
lemma-2 factor ([ left v₁ , v₃ ]) = refl
lemma-2 factor ([ right v₂ , v₃ ]) = refl
lemma-2 distrib (left ([ v₁ , v₃ ])) = refl
lemma-2 distrib (right ([ v₂ , v₃ ])) = refl
lemma-2 id v = refl
lemma-2 (c₁ + c₂) (left v₁) = cong left (lemma-2 c₁ v₁)
lemma-2 (c₁ + c₂) (right v₂) = cong right (lemma-2 c₂ v₂)
lemma-2 (c₁ × c₂) ([ v₁ , v₂ ]) = []-cong (lemma-2 c₁ v₁) (lemma-2 c₂ v₂)
-- AS IN LEMMA 1, THIS IS UNCLEAR SYNTAX
lemma-2 (c₁ ! c₂) v = trans (cong (c₂ [_]ᶠ) (lemma-2 c₁ (c₂ [ v ]ᵇ))) (lemma-2 c₂ v)
lemma-2 (symm c) v = lemma-1 c v

-- THIS IS PROPOSITION 3.2
\end{code}

%<*pi-rev>
\begin{code}
lemma-3 : ∀ {b b'}(c : comb₀ (b ↔ b'))(v : val b)
                                 → (c †) [ c [ v ]ᶠ ]ᶠ ≡ v

\end{code}
%</pi-rev>

\begin{code}
lemma-3 swap⁺ (left v) = refl
lemma-3 swap⁺ (right v) = refl
lemma-3 swapˣ ([ v₁ , v₂ ]) = refl
lemma-3 assocl⁺ (left v₁) = refl
lemma-3 assocl⁺ (right (left v₂)) = refl
lemma-3 assocl⁺ (right (right v₃)) = refl
lemma-3 assocr⁺ (left (left v₁)) = refl
lemma-3 assocr⁺ (left (right v₂)) = refl
lemma-3 assocr⁺ (right v₃) = refl
lemma-3 unite ([ [] , v ]) = refl
lemma-3 uniti v = refl
lemma-3 assoclˣ ([ v₁ , [ v₂ , v₃ ] ]) = refl
lemma-3 assocrˣ ([ [ v₁ , v₂ ] , v₃ ]) = refl
lemma-3 distrib ([ left v₁ , v₃ ]) = refl
lemma-3 distrib ([ right v₂ , v₃ ]) = refl
lemma-3 factor (left ([ v₁ , v₃ ])) = refl
lemma-3 factor (right ([ v₂ , v₃ ])) = refl
lemma-3 id v = refl
lemma-3 (c₁ + c₂) (left v₁) = cong left (lemma-3 c₁ v₁)
lemma-3 (c₁ + c₂) (right v₂) = cong right (lemma-3 c₂ v₂)
lemma-3 (c₁ × c₂) ([ v₁ , v₂ ]) = []-cong (lemma-3 c₁ v₁) (lemma-3 c₂ v₂)
lemma-3 (c₁ ! c₂) v = trans (cong ((c₁ †) [_]ᶠ) (lemma-3 c₂ (c₁ [ v ]ᶠ))) (lemma-3 c₁ v)
lemma-3 (symm c) v = lemma-2 c v

-- Toffoli gate

-- Boolean type definition
bool : 𝕓
bool = 𝟙 + 𝟙

-- Defining the AND function in the meta-language - not meant to be reversible
AND : val bool → val bool → val bool
AND (right []) (right []) = right []
AND (right []) (left []) = right []
AND (left []) (right []) = right []
AND (left []) (left []) = left []

-- Boolean NOT function
NOT : comb₀ (bool ↔ bool)
NOT = swap⁺

-- If c function - one-armed if function
if : ∀{b} → comb₀ (b ↔ b) → comb₀ ((bool × b) ↔ (bool × b))
if c = distrib ! (((id × c) + id) ! factor)

-- Defining cnot
cnot : comb₀ ((bool × bool) ↔ (bool × bool))
cnot = if NOT

-- Defining the Toffoli gate
Toffoli-gate : comb₀ ((bool × (bool × bool)) ↔ (bool × (bool × bool)))
Toffoli-gate = if cnot

-- Proof that gate works as expected
Toffoli-proof : ∀{v₁ v₂ : val bool} → Toffoli-gate [ [ v₁ , [ v₂ , (right []) ] ] ]ᶠ ≡ [ v₁ , [ v₂ , (AND v₁ v₂) ] ]
Toffoli-proof {v₁ = (right [])} {v₂ = (right [])} = refl
Toffoli-proof {v₁ = (right [])} {v₂ = (left [])} = refl
Toffoli-proof {v₁ = (left [])} {v₂ = (right [])} = refl
Toffoli-proof {v₁ = (left [])} {v₂ = (left [])} = refl

