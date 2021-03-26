\begin{code}
module Translations.T1 where

open import Data.Vec using (Vec ; _∷_ ; [] ; lookup)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ)
open import Languages.MLPi
open import Languages.Let
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; inspect ; [_] ; trans)
open import Languages.PiTyped using (𝕓 ; _+_ ; _×_ ; 𝟙 ; val ; [] ; [_,_] ; left ; right ; _[_]ᶠ ; swapˣ ; distrib ; id )
\end{code}

%<*Type-env-translate1>
\begin{code}
_ˣ : ∀{n : ℕ} → Vec 𝕓 n → 𝕓
\end{code}
%</Type-env-translate1>

%<*Type-env-translate2>
\begin{code}
([])ˣ = 𝟙
(b ∷ Γ)ˣ = ((Γ)ˣ) × b
\end{code}
%</Type-env-translate2>

%<*value-env-translate1>
\begin{code}
_ₑˣ : ∀{n : ℕ} → ∀{Γ : Vec 𝕓 n} → Γ env → val ((Γ)ˣ)
\end{code}
%</value-env-translate1>

%<*value-env-translate2>
\begin{code}
(ε)ₑˣ = []
(ρ +ₑ v)ₑˣ = [ (ρ)ₑˣ , v ]
\end{code}
%</value-env-translate2>


-- Now showing Lemma 8.1 - I don't like the way I have proved it
%<*lookup-rec1>
\begin{code}
lookupₑ : ∀{n : ℕ} → ∀(Γ : Vec 𝕓 n) → (x : Fin n) → comb (((Γ)ˣ) ↝ (lookup Γ x))
\end{code}
%</lookup-rec1>

%<*lookup-rec2>
\begin{code}
lookupₑ (b ∷ Γ) zero = sndA
\end{code}
%</lookup-rec2>

\end{code}

%<*lookup-rec>
\begin{code}

lookupₑ (b ∷ Γ) (suc m) = (first (lookupₑ Γ m)) ⋙ fstA

\end{code}
%</lookup-rec>

-- TRANSLATIONS

%<*T1>
\begin{code}
T₁ : ∀{n : ℕ} → ∀{Γ : Vec 𝕓 n} → ∀{b : 𝕓} → Γ ⊢exp∶ b → comb (((Γ)ˣ) ↝ b)
\end{code}
%</T1>

\begin{code}

T₁ []ₑ = erase
\end{code}

%<*T1-pair>
\begin{code}
T₁ {Γ = γ} (⟨ e₁ , e₂ ⟩ₑ) = (clone ((γ)ˣ)) ⋙ ((T₁ e₁) ⊗ (T₁ e₂))
\end{code}
%</T1-pair>

%<*T1-left>
\begin{code}
T₁ (leftₑ e) = (T₁ e) ⋙ leftA
\end{code}
%</T1-left>

\begin{code}

T₁ (rightₑ e) = (T₁ e) ⋙ rightA
T₁ {Γ = γ} (varₑ x) = lookupₑ γ x
T₁ (fstₑ e) = (T₁ e) ⋙ fstA
T₁ (sndₑ e) = (T₁ e) ⋙ sndA
T₁ {Γ = γ} (ₑlet e₁ ₑin e₂)  = (clone ((γ)ˣ)) ⋙ ((second (T₁ e₁)) ⋙ (T₁ e₂))

\end{code}

%<*T1-case>
\begin{code}
T₁ {Γ = γ} (ₑcase e ₑL e₁ ₑR e₂)  =
            ((clone ((γ)ˣ)) ⋙ ((first (T₁ e)) ⋙ ((arr distrib) ⋙
                      ((arr swapˣ) ⊕ (arr swapˣ))))) ⋙ (((T₁ e₁) ⊕ (T₁ e₂)) ⋙ join)
\end{code}
%</T1-case>

-- Lemma 8.2 -- T₁ preserves semantics

%<*lookup-proof>
\begin{code}
var-proof : ∀{n : ℕ} → ∀{Γ : Vec 𝕓 n} → (ρ : Γ env)
                → (x : Fin n) → ((_[_]) ρ x) ≡ ((lookupₑ Γ x) [ ((ρ)ₑˣ) ]ᵃ)
var-proof (ρ +ₑ v) zero = refl
var-proof (ρ +ₑ v) (suc n) = var-proof ρ n
\end{code}
%</lookup-proof>

\begin{code}

[]-cong : ∀ {b₁ b₂} → ∀ {x₁ x₂ : val b₁} → ∀ {y₁ y₂ : val b₂} →  x₁ ≡ x₂ → y₁ ≡ y₂ → [ x₁ , y₁ ] ≡ [ x₂ , y₂ ]
[]-cong refl refl = refl
\end{code}

%<*T1-proof>
\begin{code}
T₁-proof : ∀{n : ℕ}{Γ : Vec 𝕓 n}{b : 𝕓}
                 → (ρ : Γ env) → (e : Γ ⊢exp∶ b)
                       → evalₑ ρ e ≡ (T₁ e) [ ((ρ)ₑˣ) ]ᵃ
\end{code}
%</T1-proof>

\begin{code}
T₁-proof ρ []ₑ = refl
\end{code}
%<*T1-proof-left>
\begin{code}
T₁-proof ρ (leftₑ e) rewrite sym (T₁-proof ρ e) = refl
\end{code}
%</T1-proof-left>

\begin{code}
T₁-proof ρ (rightₑ e) rewrite sym (T₁-proof ρ e) = refl
T₁-proof ρ (⟨ e₁ , e₂ ⟩ₑ) rewrite sym (T₁-proof ρ e₁) | sym (T₁-proof ρ e₂) | (clone-proof ((ρ)ₑˣ)) = []-cong (T₁-proof ρ e₁) (T₁-proof ρ e₂)
T₁-proof ρ (varₑ x) = var-proof ρ x
T₁-proof ρ (ₑlet e₁ ₑin e₂) rewrite (T₁-proof ρ e₁) | (T₁-proof (ρ +ₑ ((T₁ e₁) [ ((ρ)ₑˣ) ]ᵃ)) e₂ ) | (clone-proof ((ρ)ₑˣ)) = refl
T₁-proof ρ (fstₑ e) with (evalₑ ρ e) | inspect (evalₑ ρ) e
...                 | ([ v₁ , v₂ ]) | [ pf ] rewrite sym (T₁-proof ρ e) | pf = refl
T₁-proof ρ (sndₑ e) with (evalₑ ρ e) | inspect (evalₑ ρ) e
...                 | ([ v₁ , v₂ ]) | [ pf ] rewrite sym (T₁-proof ρ e) | pf = refl

\end{code}

%<*T1-proof-case>
\begin{code}
T₁-proof ρ (ₑcase e ₑL e₁ ₑR e₂) with (evalₑ ρ e) | inspect (evalₑ ρ) e
...                                | left v | [ pf ]
       rewrite (clone-proof ((ρ)ₑˣ)) | (T₁-proof (ρ +ₑ v) e₁) | (trans (sym (T₁-proof ρ e)) pf) = refl
...                                | right v | [ pf ]
       rewrite (clone-proof ((ρ)ₑˣ)) | (T₁-proof (ρ +ₑ v) e₂) | (trans (sym (T₁-proof ρ e)) pf) = refl
\end{code}

%</T1-proof-case>
