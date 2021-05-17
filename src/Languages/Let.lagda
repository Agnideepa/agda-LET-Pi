\begin{code}
module Languages.Let where

open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Vec using (Vec ; [] ; _∷_ ; _[_]=_ ; here ; there ; lookup)
open import Data.Fin using (Fin; zero; suc)
open import Languages.MLPi
open import Languages.PiTyped using (𝕓 ; _+_ ; _×_ ; 𝟙 ; val ; [] ; [_,_] ; left ; right)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

-- Now we work with environments
\end{code}

%<*env-declare>
\begin{code}
data _env : ∀{n : ℕ} → (Vec 𝕓 n) → Set where
  ε : [] env
  _+ₑ_ : ∀{n : ℕ}{Γ : Vec 𝕓 n}{b : 𝕓}
         → Γ env
         → (x : val b)
        ----------
         → (b ∷ Γ) env
\end{code}
%</env-declare>


\begin{code}

_[_] : ∀{n : ℕ}{Γ : Vec 𝕓 n}{x : Fin n}{b : 𝕓} → Γ env → Γ [ x ]= b → val b
(ρ +ₑ v) [ here ] = v
(ρ +ₑ _) [ there m ] = ρ [ m ]

-- Typing Rules and forming expressions

data _⊢exp∶_ : ∀{n : ℕ} → ∀(Γ : Vec 𝕓 n) → 𝕓 → Set where
  []ₑ : ∀{n : ℕ}{Γ : Vec 𝕓 n}
        ----------
        → Γ ⊢exp∶ 𝟙
  leftₑ : ∀{n : ℕ}{b₁ b₂ : 𝕓}{Γ : Vec 𝕓 n}
        → Γ ⊢exp∶ b₁
        ----------
        → Γ ⊢exp∶ (b₁ + b₂)
  rightₑ : ∀{n : ℕ}{b₁ b₂ : 𝕓}{Γ : Vec 𝕓 n}
        → Γ ⊢exp∶ b₂
        ----------
        → Γ ⊢exp∶ (b₁ + b₂)
\end{code}

%<*debruijn>
\begin{code}
  varₑ : ∀{n : ℕ}{b : 𝕓}
            {Γ : Vec 𝕓 n}{x : Fin n}
        → Γ [ x ]= b
        ----------
        → Γ ⊢exp∶ b
\end{code}
%</debruijn>

\begin{code}
  ₑlet_ₑin_ :  ∀{n : ℕ}{b₁ b₂ : 𝕓}{Γ : Vec 𝕓 n}
        → Γ ⊢exp∶ b₁
        → (b₁ ∷ Γ) ⊢exp∶ b₂
        ----------
        → Γ ⊢exp∶ b₂
\end{code}
%<*fst-example>
\begin{code}
  fstₑ : ∀{n : ℕ}{b₁ b₂ : 𝕓}{Γ : Vec 𝕓 n}
        → Γ ⊢exp∶ (b₁ × b₂)
        ----------
        → Γ ⊢exp∶ b₁
\end{code}
%</fst-example>
\begin{code}
  sndₑ : ∀{n : ℕ}{b₁ b₂ : 𝕓}{Γ : Vec 𝕓 n}
        → Γ ⊢exp∶ (b₁ × b₂)
        ----------
        → Γ ⊢exp∶ b₂
  ⟨_,_⟩ₑ :  ∀{n : ℕ}{b₁ b₂ : 𝕓}{Γ : Vec 𝕓 n}
        → Γ ⊢exp∶ b₁
        → Γ ⊢exp∶ b₂
        ----------
        → Γ ⊢exp∶ (b₁ × b₂)
\end{code}

%<*case-example>
\begin{code}
  ₑcase_ₑL_ₑR_ : ∀{n : ℕ}{b₁ b₂ b₃ : 𝕓}
                            {Γ : Vec 𝕓 n}
        → Γ ⊢exp∶ (b₁ + b₂)
        → (b₁ ∷ Γ) ⊢exp∶ b₃
        → (b₂ ∷ Γ) ⊢exp∶ b₃
        ----------
        → Γ ⊢exp∶ b₃
\end{code}
%</case-example>

\begin{code}

-- EVALUATION
\end{code}

%<*eval-declare>
\begin{code}
evalₑ : ∀{n : ℕ}{Γ : Vec 𝕓 n}{b : 𝕓}
           → Γ env → Γ ⊢exp∶ b → val b
\end{code}
%</eval-declare>

\begin{code}
evalₑ _ []ₑ = []
\end{code}

%<*left>
\begin{code}
evalₑ ρ (leftₑ e) = left (evalₑ ρ e)
evalₑ ρ (ₑlet e₁ ₑin e₂) = evalₑ (ρ +ₑ (evalₑ ρ e₁)) e₂
\end{code}
%</left>

\begin{code}
evalₑ ρ (rightₑ e) = right (evalₑ ρ e)
evalₑ ρ (varₑ x) = ρ [ x ]
\end{code}

\begin{code}
evalₑ ρ (fstₑ e) with (evalₑ ρ e)
...                 | [ v₁ , v₂ ] = v₁
evalₑ ρ (sndₑ e) with (evalₑ ρ e)
...                 | [ v₁ , v₂ ] = v₂
evalₑ ρ (⟨ e₁ , e₂ ⟩ₑ) = [ (evalₑ ρ e₁) , (evalₑ ρ e₂) ]
evalₑ ρ (ₑcase e ₑL e₁ ₑR e₂) with (evalₑ ρ e)
...                 | (left v) = evalₑ (ρ +ₑ v) e₁
...                 | (right v) = evalₑ (ρ +ₑ v) e₂

\end{code}


