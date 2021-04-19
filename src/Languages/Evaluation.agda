module Languages.Evaluation where

open import Data.Nat using (ℕ ; suc ; zero; _+_)
open import Data.Vec using (Vec ; [] ; _∷_ ; _[_]=_ ; here ; there ; lookup; _++_)
open import Data.Fin using (Fin; zero; suc)
open import Languages.Let
open import Languages.PiTyped using (𝕓 ; _×_ ; _+_ ; 𝟙 ; val ; [] ; [_,_] ; left ; right ; bool)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

bool-env : (n : ℕ) → Vec 𝕓 n
bool-env zero = []
bool-env (suc n) = bool ∷ (bool-env n)

replace-helper : ∀{n : ℕ} → (m : ℕ)  → Fin (Data.Nat._+_ m n) → Fin (Data.Nat._+_ m (suc n))
replace-helper zero x = suc x
replace-helper (suc m) zero = zero
replace-helper (suc m) (suc x) = suc (replace-helper m x)

replace-var : ∀{n : ℕ} → ∀(m : ℕ) → {Γ₁ : Vec 𝕓 m}{Γ₂ : Vec 𝕓 n}{b b' : 𝕓}{x : Fin (Data.Nat._+_ m n)} → (Γ₁ ++ Γ₂) [ x ]= b → ((Γ₁ ++ (b' ∷ Γ₂))) [ (replace-helper m x) ]= b
replace-var zero {Γ₁ = []} x = (there x)
replace-var (suc m) {Γ₁ = x₁ ∷ Γ₁'} here = here
replace-var (suc m) {Γ₁ = x₁ ∷ Γ₁'} (there x) = there (replace-var m x)

replace : ∀{n : ℕ} → ∀(m : ℕ) → {Γ₁ : Vec 𝕓 m}{Γ₂ : Vec 𝕓 n}{b b' : 𝕓} → (Γ₁ ++ Γ₂) ⊢exp∶ b → ((Γ₁ ++ (b' ∷ Γ₂))) ⊢exp∶ b
replace m []ₑ = []ₑ
replace m (leftₑ e) = leftₑ (replace m e)
replace m (rightₑ e) = rightₑ (replace m e)
replace m (fstₑ e) = fstₑ (replace m e)
replace m (sndₑ e) = sndₑ (replace m e)
replace m (varₑ x) = varₑ (replace-var m x)
replace m {Γ₂ = Γ₂} (ₑlet e₁ ₑin e₂) = ₑlet (replace m e₁) ₑin (replace (suc m) {Γ₂ = Γ₂} e₂)
replace m (⟨ e₁ , e₂ ⟩ₑ) = ⟨ (replace m e₁) , (replace m e₂) ⟩ₑ
replace m {Γ₂ = Γ₂} (ₑcase e ₑL e₁ ₑR e₂) = ₑcase (replace m e) ₑL (replace (suc m) {Γ₂ = Γ₂} e₁) ₑR (replace (suc m) {Γ₂ = Γ₂} e₂)

not : ∀{n : ℕ}{Γ : Vec 𝕓 n} → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool
not e = ₑcase e ₑL (rightₑ []ₑ) ₑR (leftₑ []ₑ)

and : ∀{n : ℕ}{Γ : Vec 𝕓 n} → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool
and e₁ e₂ = ₑcase e₁ ₑL (leftₑ []ₑ) ₑR (replace zero {Γ₁ = []} e₂)

or : ∀{n : ℕ}{Γ : Vec 𝕓 n} → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool
or e₁ e₂ = ₑcase e₁ ₑL (replace zero {Γ₁ = []} e₂) ₑR (rightₑ []ₑ)

xor : ∀{n : ℕ}{Γ : Vec 𝕓 n} → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool
xor e₁ e₂ = or (and e₁ (not e₂)) (and (not e₁) e₂)

-- OR gate with n inputs
or-gate : ∀(n : ℕ) → (bool-env n) ⊢exp∶ bool
or-gate zero = leftₑ []ₑ
or-gate (suc n) = or (varₑ here) (replace zero {Γ₁ = []} (or-gate n))

-- AND gate with n inputs
and-gate : ∀(n : ℕ) → (bool-env n) ⊢exp∶ bool
and-gate zero = rightₑ []ₑ
and-gate (suc n) = and (varₑ here) (replace zero {Γ₁ = []} (and-gate n))

-- XOR gate with n inputs
xor-gate : ∀(n : ℕ) → (bool-env n) ⊢exp∶ bool
xor-gate zero = leftₑ []ₑ
xor-gate (suc n) = xor (varₑ here) (replace zero {Γ₁ = []} (xor-gate n))

-- Computing the carry bit
carry : ∀{n : ℕ}{Γ : Vec 𝕓 n} → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool
carry e₁ e₂ e₃ = or (or (and (not e₁) (and e₂ e₃)) (and (not e₃) (and e₁ e₂))) (or (and (not e₂) (and e₃ e₁)) (and e₁ (and e₂ e₃)))

-- XOR as required by full adder
3-xor : ∀{n : ℕ}{Γ : Vec 𝕓 n} → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool → Γ ⊢exp∶ bool
3-xor e₁ e₂ e₃ = xor (e₁) (xor e₂ e₃)

-- Testing the truth table of carry function
lemma-0 : evalₑ ε (carry (leftₑ []ₑ) (leftₑ []ₑ) (leftₑ []ₑ)) ≡ left []
lemma-1 : evalₑ ε (carry (leftₑ []ₑ) (leftₑ []ₑ) (rightₑ []ₑ)) ≡ left []
lemma-2 : evalₑ ε (carry (leftₑ []ₑ) (rightₑ []ₑ) (leftₑ []ₑ)) ≡ left []
lemma-3 : evalₑ ε (carry (leftₑ []ₑ) (rightₑ []ₑ) (rightₑ []ₑ)) ≡ right []
lemma-4 : evalₑ ε (carry (rightₑ []ₑ) (leftₑ []ₑ) (leftₑ []ₑ)) ≡ left []
lemma-5 : evalₑ ε (carry (rightₑ []ₑ) (leftₑ []ₑ) (rightₑ []ₑ)) ≡ right []
lemma-6 : evalₑ ε (carry (rightₑ []ₑ) (rightₑ []ₑ) (leftₑ []ₑ)) ≡ right []
lemma-7 : evalₑ ε (carry (rightₑ []ₑ) (rightₑ []ₑ) (rightₑ []ₑ)) ≡ right []

lemma-0 = refl
lemma-1 = refl
lemma-2 = refl
lemma-3 = refl
lemma-4 = refl
lemma-5 = refl
lemma-6 = refl
lemma-7 = refl

-- Defining a full adder
adder-in : (n : ℕ) → 𝕓
adder-in zero = 𝟙
adder-in (suc zero) = bool
adder-in (suc (suc n)) = (adder-in (suc n)) × bool

adder-res : (n : ℕ) → 𝕓
adder-res zero = bool
adder-res (suc n) = (adder-res n) × bool

--nat-to-here : ∀{n : ℕ}{Γ : Vec 𝕓 n} → (x : Fin n) → Γ [ x ]= (lookup Γ x)
--nat-to-here {Γ = b ∷ γ} zero = here
--nat-to-here {Γ = b ∷ γ} (suc m) = there (nat-to-here {Γ = γ} m)

full-adder : ∀{n : ℕ}{Γ : Vec 𝕓 n} → (m : ℕ) → Γ ⊢exp∶ adder-in(m) → Γ ⊢exp∶ adder-in(m) → Γ ⊢exp∶ bool → Γ ⊢exp∶ adder-res(m)
full-adder zero e₁ e₂ e₃ = e₃
full-adder (suc zero) e₁ e₂ e₃ = ⟨ (carry e₁ e₂ e₃) , (3-xor e₁ e₂ e₃) ⟩ₑ
full-adder (suc (suc n)) e₁ e₂ e₃ = ⟨ (full-adder (suc n) (fstₑ e₁) (fstₑ e₂) (carry (sndₑ e₁) (sndₑ e₂) e₃)) , (3-xor (sndₑ e₁) (sndₑ e₂) e₃) ⟩ₑ

adder-env : ∀(n : ℕ) → Vec 𝕓 2
adder-env n = (adder-in n) ∷ ((adder-in n) ∷ [])

full-adder-wrapper : ∀(n : ℕ) → (adder-env n) ⊢exp∶ adder-res(n)
full-adder-wrapper n = full-adder n (varₑ here) (varₑ (there here)) (leftₑ []ₑ)

test : val bool
test = evalₑ ((ε +ₑ (left [])) +ₑ (right [])) (not (and (varₑ here) (or (varₑ (there here)) (varₑ (there here)))))

lemma : evalₑ ((ε +ₑ (left [])) +ₑ (right [])) (not (and (varₑ here) (or (varₑ (there here)) (varₑ (there here))))) ≡ right []
lemma = refl
