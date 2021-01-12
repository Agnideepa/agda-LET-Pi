module Translations.T2 where

open import Languages.MLPi
open import Languages.PiTyped
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Product using (Σ ; _,_)

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

-- Lemma 9.1 - T₂ preserves semantics

T₂-proof : ∀{b₁ b₂} → (c : comb (b₁ ↝ b₂)) → (v : val b₁) → Σ (val (garbage(c))) (λ g' → ((T₂ c) [ ([ φ(heap(c)) , v ]) ]ᶠ) ≡ ([ g' , (c [ v ]ᵃ) ]))
T₂-proof (arr c) v = [] , refl
T₂-proof (create _) [] = [] , refl
T₂-proof (erase) v = v , refl
T₂-proof (a₁ ⊗ a₂) ([ v₁ , v₂ ]) with (T₂-proof a₁ v₁) | (T₂-proof a₂ v₂)
...                                 | (g₁ , pf₁) | (g₂ , pf₂) rewrite pf₁ | pf₂ = ([ g₁ , g₂ ]) , refl
T₂-proof (first a) ([ v ,  v' ]) with (T₂-proof a v)
...                                 | (g , pf) rewrite pf = g , refl
T₂-proof (a₁ ⋙ a₂) v with (T₂-proof a₁ v) | (T₂-proof a₂ (a₁ [ v ]ᵃ))
...                     | (g₁ , pf₁) | (g₂ , pf₂) rewrite pf₁ | pf₂ = ([ g₂ , g₁ ]) , refl
T₂-proof {b₂ = b' + b''} (left a) (left v) with (T₂-proof a v)
...                             | (g , pf) rewrite pf = (left ([ g , ([ φ(b') , (left(φ(b'')))]) ])) , refl
T₂-proof {b₂ = b' + b''} (left a) (right v) = (right ([ ([ φ(heap(a)) , left(φ(b')) ]) , φ(b'') ])) , refl
T₂-proof {b₂ = b' + b''} (a₁ ⊕ a₂) (left v₁) with (T₂-proof a₁ v₁)
...                                             | (g₁ , pf₁) rewrite pf₁ = (left ([ ([ g₁ , φ(heap(a₂)) ]) , ([ φ(b') , (left (φ(b''))) ]) ])) , refl
T₂-proof {b₂ = b' + b''} (a₁ ⊕ a₂) (right v₂) with (T₂-proof a₂ v₂)
...                                             | (g₂ , pf₂) rewrite pf₂ = (right ([ ([ g₂ , ([ φ(heap(a₁)) , (left (φ(b'))) ]) ]) , φ(b'') ])) , refl
