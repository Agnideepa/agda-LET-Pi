module Languages.Pi where

-- Type universe -- should combinator types be separate from value types?

data 𝕓 : Set where
  𝟙 : 𝕓
  _×_ _+_ : 𝕓 → 𝕓 → 𝕓

data 𝕔 : Set where
  _↔_ : 𝕓 → 𝕓 → 𝕔

-- Do we need to map the above types into Agda sets? Why does one of the links do this?

data v : Set where
  unit : v
  left right : v → v
  [_,_] : v → v → v

-- Why do we need sym?

data c : Set where
  swap⁺ assocl⁺ assocr⁺ unite uniti swapˣ assoclˣ assocrˣ distrib factor id : c
  _+_ _×_ _!_ : c → c → c
  sym : c → c

{- Defining values and types together? ⇓ was an odd choice but Agda did
not allow :
-}

data ⊢_⇓_ : v → 𝕓 → Set where
  unit : ⊢ unit ⇓ 𝟙
  _×_ : ∀{v₁ v₂} {b₁ b₂}
         → ⊢ v₁ ⇓ b₁
         → ⊢ v₂ ⇓ b₂
            -----------
         → ⊢ [ v₁ , v₂ ] ⇓ (b₁ × b₂)
  left : ∀{v} {b₁ b₂}
         → ⊢ v ⇓ b₁
            -----------
         → ⊢ left v ⇓ (b₁ + b₂)
  right : ∀{v} {b₁ b₂}
         → ⊢ v ⇓ b₂
            -----------
         → ⊢ right v ⇓ (b₁ + b₂)

{- An alternate way the above could have been defined
  data Π : 𝕓 → Set where
    unit : Π 𝟙
    _×_ : ∀{b₁ b₂}
         → Π b₁
         → Π b₂
            -----------
         → Π (b₁ × b₂)
  ..and so on - meaning we would not need to define values separately.
  
-}

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
  sym : ∀{b₁ b₂}
        → comb (b₁ ↔ b₂)
        ----------------
        → comb (b₂ ↔ b₁)
  
_† : ∀{b b' : 𝕓} → comb (b ↔ b') → comb (b' ↔ b)
--_† : c → c
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
(sym c)† = c

