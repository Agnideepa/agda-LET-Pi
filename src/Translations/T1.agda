module Translations.T1 where

open import Data.Vec using (Vec ; _∷_ ; [])
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ)
open import Languages.MLPi
open import Languages.Let
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; sym ; cong ; inspect ; [_] ; trans ; subst)
open Eq.≡-Reasoning using (begin_; step-≡; _∎ ; _≡⟨⟩_)

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

-- Lemma 8.2

var-proof : ∀{n : ℕ} → ∀{Γ : Vec 𝕓 n} → (ρ : Γ env) → (x : Fin n) → ((_[_]) ρ x) ≡ ((lookup Γ x) [ ((ρ)ₑˣ) ]ᵃ)
var-proof (ρ +ₑ v) zero = refl
var-proof (ρ +ₑ v) (suc n) = var-proof ρ n

[]-cong : ∀ {b₁ b₂} → ∀ {x₁ x₂ : val b₁} → ∀ {y₁ y₂ : val b₂} →  x₁ ≡ x₂ → y₁ ≡ y₂ → [ x₁ , y₁ ] ≡ [ x₂ , y₂ ]
[]-cong refl refl = refl

{-# TERMINATING #-}
T₁-proof : {n : ℕ} → {Γ : Vec 𝕓 n} → {b : 𝕓} → (ρ : Γ env) → ∀(e : Γ ⊢exp∶ b) → (evalₑ ρ e) ≡ ((T₁ e) [ ((ρ)ₑˣ) ]ᵃ)

T₁-proof ρ (valₑ []) = refl
T₁-proof {b = b₁ + b₂} ρ (valₑ (left v)) rewrite sym (T₁-proof ρ (valₑ v)) | sym (leftA-proof {b₁ = b₁} {b₂ = b₂} {v = v}) = refl
T₁-proof {b = b₁ + b₂} ρ (valₑ (right v)) rewrite sym (T₁-proof ρ (valₑ v)) | sym (rightA-proof {b₁ = b₁} {b₂ = b₂} {v = v}) = refl
T₁-proof {Γ = γ} ρ (valₑ [ v₁ , v₂ ]) rewrite  sym (T₁-proof ρ (valₑ v₁)) | sym (T₁-proof ρ (valₑ v₂)) | (clone-proof {b = ((γ)ˣ)} ((ρ)ₑˣ)) = []-cong (T₁-proof ρ (valₑ v₁)) (T₁-proof ρ (valₑ v₂))
T₁-proof {b = b₁ + b₂} ρ (leftₑ e) rewrite sym (T₁-proof ρ e) | sym (leftA-proof {b₁ = b₁} {b₂ = b₂} {v = (evalₑ ρ e)}) = refl
T₁-proof {b = b₁ + b₂} ρ (rightₑ e) rewrite sym (T₁-proof ρ e) | sym (rightA-proof {b₁ = b₁} {b₂ = b₂} {v = (evalₑ ρ e)}) = refl
T₁-proof {Γ = γ} ρ (< e₁ , e₂ >ₑ) rewrite  sym (T₁-proof ρ e₁) | sym (T₁-proof ρ e₂) | (clone-proof {b = ((γ)ˣ)} ((ρ)ₑˣ)) = []-cong (T₁-proof ρ e₁) (T₁-proof ρ e₂)
T₁-proof ρ (varₑ x) = var-proof ρ x
T₁-proof {Γ = γ} ρ (ₑlet e₁ ₑin e₂) rewrite (T₁-proof ρ e₁) | (T₁-proof (ρ +ₑ ((T₁ e₁) [ ((ρ)ₑˣ) ]ᵃ)) e₂ ) | (clone-proof {b = ((γ)ˣ)} ((ρ)ₑˣ)) = refl
T₁-proof ρ (fstₑ e) with (evalₑ ρ e) | inspect (evalₑ ρ) e
...                 | ([ v₁ , v₂ ]) | [ pf ] rewrite sym (T₁-proof ρ e) | pf | sym (fstA-proof {v₁ = v₁} {v₂ = v₂}) = refl
T₁-proof ρ (sndₑ e) with (evalₑ ρ e) | inspect (evalₑ ρ) e
...                 | ([ v₁ , v₂ ]) | [ pf ] rewrite sym (T₁-proof ρ e) | pf | sym (sndA-proof {v₁ = v₁} {v₂ = v₂}) = refl
T₁-proof {Γ = γ} ρ (ₑcase e ₑL e₁ ₑR e₂) with (evalₑ ρ e) | inspect (evalₑ ρ) e
...                                   | left v | [ pf ] rewrite (clone-proof {b = ((γ)ˣ)} ((ρ)ₑˣ)) | (T₁-proof (ρ +ₑ v) e₁) | (trans (sym (T₁-proof ρ e)) pf) = refl
...                                   | right v | [ pf ] rewrite (clone-proof {b = ((γ)ˣ)} ((ρ)ₑˣ)) | (T₁-proof (ρ +ₑ v) e₂) | (trans (sym (T₁-proof ρ e)) pf) = refl 

{-
T₁-proof : ∀{n : ℕ} → ∀{Γ : Vec 𝕓 n} → ∀{b : 𝕓} → ∀{v : val b} → (ρ : Γ env) → (e : Γ ⊢exp∶ b) → {ev : (evalₑ ρ e) ≡ v} → ((T₁ e) [ ((ρ)ₑˣ) ]ᵃ) ≡ v
T₁-proof ρ (valₑ []) {ev = eq} rewrite eq = refl
T₁-proof ρ (valₑ [ v₁ , v₂ ]) {ev = eq} rewrite eq | sym (T₁-proof ρ (valₑ v₁)) | sym (T₁-proof ρ (valₑ v₂)) = refl
-}



