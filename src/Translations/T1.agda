module Translations.T1 where

open import Data.Vec using (Vec ; _∷_ ; [])
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ)
open import Languages.MLPi
open import Languages.Let

_ˣ : ∀{n : ℕ} → Vec 𝕓 n → 𝕓
([])ˣ = 𝟙
(b ∷ bs)ˣ = ((bs)ˣ) × b

_ₑˣ : ∀{n : ℕ} → ∀{Γ : Vec 𝕓 n} → Γ env → val ((Γ)ˣ)
(ε)ₑˣ = []
(ρ +ₑ v)ₑˣ = [ (ρ)ₑˣ , v ]

-- Now showing Lemma 8.1 - I don't like the way I have proved it

lookup : ∀{n : ℕ} → ∀(Γ : Vec 𝕓 n) → (x : Fin n) → comb (((Γ)ˣ) ↝ (Vec-elem Γ x))
lookup (b ∷ bs) zero = sndA
lookup (b ∷ bs) (suc m) = ((lookup bs m) ⊗ (arr id)) ⋙ fstA

-- TRANSLATIONS

T₁ : ∀{n : ℕ} → ∀{Γ : Vec 𝕓 n} → ∀{b : 𝕓} → Γ ⊢exp∶ b → comb (((Γ)ˣ) ↝ b)
T₁ (valₑ []) = erase
T₁ {Γ = γ} (valₑ [ v₁ , v₂ ]) = (clone ((γ)ˣ)) ⋙ ((T₁ (valₑ v₁)) ⊗ (T₁ (valₑ v₂)))
T₁ (valₑ (left v)) = (T₁ (valₑ v)) ⋙ leftA
T₁ (valₑ (right v)) = (T₁ (valₑ v)) ⋙ rightA
T₁ {Γ = γ} (< e₁ , e₂ >ₑ) = (clone ((γ)ˣ)) ⋙ ((T₁ e₁) ⊗ (T₁ e₂))
T₁ (leftₑ e) = (T₁ e) ⋙ leftA
T₁ (rightₑ e) = (T₁ e) ⋙ rightA
T₁ {Γ = γ} (varₑ x) = lookup γ x
T₁ (fstₑ e) = (T₁ e) ⋙ fstA
T₁ (sndₑ e) = (T₁ e) ⋙ sndA
T₁ {Γ = γ} (ₑlet e₁ ₑin e₂)  = (clone ((γ)ˣ)) ⋙ ((second (T₁ e₁)) ⋙ (T₁ e₂))
T₁ {Γ = γ} (ₑcase e ₑL e₁ ₑR e₂)  = ((clone ((γ)ˣ)) ⋙ ((first (T₁ e)) ⋙ ((arr distrib) ⋙ ((arr swapˣ) ⊕ (arr swapˣ))))) ⋙ (((T₁ e₁) ⊕ (T₁ e₂)) ⋙ join)


