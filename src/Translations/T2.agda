module Translations.T2 where

open import Languages.MLPi
open import Languages.PiTyped

heap : ∀{b₁ b₂} → comb (b₁ ↝ b₂) → 𝕓
garbage : ∀{b₁ b₂} → comb (b₁ ↝ b₂) → 𝕓

heap (arr _) = 𝟙
heap (a₁ ⋙ a₂) = (heap a₁) × (heap a₂)
heap (a₁ ⊗ a₂) = (heap a₁) × (heap a₂)
heap (first a) = heap a
heap (create b) = b
heap (erase) = 𝟙
heap {b₂ = b' + b''} (left a) = (heap a) × ((b' + b'') × (b'' + b'))
heap {b₂ = b' + b''} (a₁ ⊕ a₂) = ((heap a₁) × (heap a₂)) × ((b' + b'') × (b'' + b'))

garbage (arr _) = 𝟙
garbage (a₁ ⋙ a₂) = (garbage a₂) × (garbage a₁)
garbage (a₁ ⊗ a₂) = (garbage a₁) × (garbage a₂)
garbage (first a) = garbage a
garbage (create b) = 𝟙
garbage (erase {b = b₁}) = b₁
garbage {b₂ = b' + b''} (left a) = ((garbage a) × (b' × (b'' + b'))) + (((heap a) × (b' + b'')) × b'')
garbage {b₂ = b' + b''} (a₁ ⊕ a₂) = (((garbage a₁) × (heap a₂)) × (b' × (b'' + b'))) + (((garbage a₂) × ((heap a₁) × (b' + b''))) × b'')

T₂ : ∀{b₁ b₂} → (c : comb (b₁ ↝ b₂)) → comb₀ ((heap(c) × b₁) ↔ (garbage(c) × b₂))
T₂ (arr c) = id × c
T₂ (a₁ ⋙ a₂) = ((((swapˣ × id) ! assocrˣ) ! (id × (T₂ a₁))) ! ((id × swapˣ) ! assoclˣ)) ! (((T₂ a₂) × id) ! (assocrˣ ! ((id × swapˣ) ! assoclˣ)))
T₂ (a₁ ⊗ a₂) = shuffle ! (((T₂ a₁) × (T₂ a₂)) ! shuffle)
T₂ (first a) = assoclˣ ! (((T₂ a) × id) ! assocrˣ)
T₂ (create _) = swapˣ
T₂ (erase) = swapˣ
T₂ (left a) = ((swapˣ ! distrib) ! (((assoclˣ ! (((swapˣ ! (T₂ a)) × id) ! assocrˣ)) ! ((id × (assoclˣ ! (((swapˣ ! leftSwap) × id) ! (assocrˣ ! swapˣ)))) ! assoclˣ)) + ((assoclˣ ! ((swapˣ × id) ! assocrˣ)) ! ((id × ((assoclˣ ! ((swapˣ × id) ! assocrˣ)) ! (id × (swapˣ ! (leftSwap ! (swap⁺ × id)))))) ! (assoclˣ ! ((id × swapˣ) ! assoclˣ)))))) ! factor
T₂ (a₁ ⊕ a₂) = ((swapˣ ! distrib) ! (((((assoclˣ ! ((assoclˣ ! ((swapˣ ! (T₂ a₁)) × id)) × id)) ! ((assocrˣ ! assocrˣ) ! (id × (assoclˣ ! ((swapˣ × id) ! assocrˣ))))) ! (id × (id × ((assoclˣ ! ((swapˣ ! leftSwap) × id)) ! (assocrˣ ! swapˣ))))) ! (assoclˣ ! assoclˣ)) + (((assoclˣ ! ((((id × swapˣ) ! assoclˣ) ! ((swapˣ ! (T₂ a₂)) × id)) × id)) ! (assocrˣ ! assocrˣ)) ! ((id × ((assoclˣ ! ((id × swapˣ) ! shuffle)) ! ((((swapˣ ! leftSwap) ! (swap⁺ × id)) × id) ! (swapˣ ! (id × swapˣ))))) ! (assoclˣ ! assoclˣ))))) ! factor


