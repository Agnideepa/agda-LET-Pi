module Languages.PiCirc where

open import Data.Empty
  using ( ⊥-elim )

open import Data.Fin
  using ( Fin ; zero ; suc ; fromℕ ; toℕ ; _ℕ-_ ; Fin′ ; inject ; inject! ; inject₁ ; _≤_)

open import Data.Nat
  using ( ℕ ; zero ; suc )

open import Function
  using ( _∘_ )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; refl ; sym ; cong ; trans ; inspect ; [_])

open import Relation.Nullary
  using ( ¬_ ; Dec ; yes ; no )

data 𝕓 : ℕ → Set where
  𝟙 : {n : ℕ} → 𝕓 n
  _×_ _+_ :  ∀{n : ℕ}
           → 𝕓 n
           → 𝕓 n
           --------
           → 𝕓 n
  ref_ : ∀{n : ℕ}
         → Fin n
         ----------
         → 𝕓 n
  μ_ : ∀{n : ℕ}
       → 𝕓 (suc n)
       ------------
       → 𝕓 n

-- THE FOLLOWING CODE IS FROM https://github.com/zmthy/recursive-types WITH VERY SLIGHT MODIFICATIONS TO MATCH OUR NOTATION

inc : ∀ {n} → 𝕓 n → 𝕓 (suc n)
inc 𝟙     = 𝟙
inc (b₁ × b₂) = (inc b₁) × (inc b₂)
inc (b₁ + b₂) = (inc b₁) + (inc b₂)
inc (μ b)   = μ (inc b)
inc (ref x) = ref (suc x)

-- A proposition that the indexed number is the largest it can be, i.e. one less
-- than its exclusive upper bound.
data Max : ∀ {n} → Fin n → Set where
  max : ∀ {n} → Max {suc n} (fromℕ n)

-- A lemma on Max: if a number is max, then one less than that number with a
-- simultaneously lowered upper bound is also max.
max-pre : ∀ {n} {x : Fin (suc n)} → Max (suc x) → Max x
max-pre max = max

-- A lemma on Max: if a number is max, then one more than that number with a
-- simultaneously increased upper bound is also max.
max-suc : ∀ {n} {x : Fin n} → Max x → Max (suc x)
max-suc max = max

-- Given a proof that a number is not max, reduce its lower bound by one,
-- keeping the value of the number the same.
reduce : ∀ {n} {x : Fin (suc n)} → ¬ Max x → Fin n
reduce {zero}  {zero}   ¬p = ⊥-elim (¬p max)
reduce {zero}  {suc ()} ¬p
reduce {suc n} {zero}   ¬p = zero
reduce {suc n} {suc x}  ¬p = suc (reduce {x = x} (¬p ∘ max-suc))

-- Max is a decidable proposition: just compare the number value to the value of
-- the upper bound.
max? : ∀ {n} (x : Fin n) → Dec (Max x)
max? {zero}        ()
max? {suc zero}    zero     = yes max
max? {suc zero}    (suc ())
max? {suc (suc n)} zero     = no (λ ())
max? {suc (suc n)} (suc x)  with max? x
max? {suc (suc n)} (suc .(fromℕ n)) | yes max = yes max
max? {suc (suc n)} (suc x)          | no ¬p = no (¬p ∘ max-pre)

-- Substitute a type as the largest reference in another type, reducing the
-- number of references as a result.
_[_] : ∀ {n} → 𝕓 (suc n) → 𝕓 n → 𝕓 n
𝟙 [ A ] = 𝟙
(b₁ × b₂) [ A ] = (_[_] b₁ A) × (_[_] b₂ A)
(b₁ + b₂) [ A ] = (_[_] b₁ A) + (_[_] b₂ A)
(μ b)   [ A ] = μ (_[_] b (inc A))
(ref x)  [ A ] with max? x
(ref ._)  [ A ] | yes max  = A
(ref x)   [ A ] | no ¬p    = ref (reduce ¬p)

--- END OF CODE FROM https://github.com/zmthy/recursive-types WITH VERY SLIGHT MODIFICATIONS TO MATCH OUR NOTATION

{- OWN FAILED ATTEMPT AT SUBSTITUTION
subst : ∀{n : ℕ}{m : Fin (suc n)} → 𝕓 n → (x : Fin n) → 𝕓 (toℕ m) → 𝕓 ((toℕ x) Data.Nat.+ toℕ(m))
subst 𝟙 _ _ = 𝟙
subst (b₁ × b₂) x u = (subst b₁ x u) × (subst b₂ x u)
subst (b₁ + b₂) x u = (subst b₁ x u) + (subst b₂ x u)
subst (ref zero) zero u = u
subst (ref (suc m)) (suc n) u = subst (ref m) n u
subst (ref x) _ _ = ref x
subst (μ b) x u = μ (b (suc x) u)
-}

data val : (n : ℕ) → 𝕓 n → Set where
  [] : ∀{n} → val n 𝟙
  [_,_] : ∀{n}{b₁ b₂ : 𝕓 n}
        → val n b₁
        → val n b₂
       -----------
        → val n (b₁ × b₂)
  left :  ∀{n}{b₁ b₂ : 𝕓 n}
        → val n b₁
       -----------
        → val n (b₁ + b₂)
  right : ∀{n}{b₁ b₂ : 𝕓 n}
        → val n b₂
       -----------
        → val n (b₁ + b₂)
  ⟨_⟩ : ∀{n}{b : 𝕓 (suc n)}
        → val n (_[_] b (μ b))
       ---------------
        → val n (μ b)

{-data val : 𝕓 0 → Set where
  [] : val 𝟙
  [_,_] : {b₁ b₂ : 𝕓 0}
        → val b₁
        → val b₂
       -----------
        → val (b₁ × b₂)
  left :  {b₁ b₂ : 𝕓 0}
        → val b₁
       -----------
        → val (b₁ + b₂)
  right : {b₁ b₂ : 𝕓 0}
        → val b₂
       -----------
        → val (b₁ + b₂)
  ⟨_⟩ : {b : 𝕓 (suc zero)}
        → val (_[_] b (μ b))
       ---------------
        → val (μ b)
-}

data _⇌_ : {n : ℕ} →  𝕓 n → 𝕓 n → Set where
  swap⁺ : ∀{n}{b₁ b₂ : 𝕓 n} → (b₁ + b₂) ⇌ (b₂ + b₁)
  swapˣ : ∀{n}{b₁ b₂ : 𝕓 n} → (b₁ × b₂) ⇌ (b₂ × b₁)
  assocl⁺ : ∀{n}{b₁ b₂ b₃ : 𝕓 n} → (b₁ + (b₂ + b₃)) ⇌ ((b₁ + b₂) + b₃)
  assocr⁺ : ∀{n}{b₁ b₂ b₃ : 𝕓 n}→ ((b₁ + b₂) + b₃) ⇌ (b₁ + (b₂ + b₃))
  assoclˣ : ∀{n}{b₁ b₂ b₃ : 𝕓 n} → (b₁ × (b₂ × b₃)) ⇌ ((b₁ × b₂) × b₃)
  assocrˣ : ∀{n}{b₁ b₂ b₃ : 𝕓 n} → ((b₁ × b₂) × b₃) ⇌ (b₁ × (b₂ × b₃))
  fold : ∀{n}{b : 𝕓 (suc n)} → (_[_] b (μ b)) ⇌ (μ b)
  unfold : ∀{n}{b : 𝕓 (suc n)} → (μ b) ⇌ (_[_] b (μ b))
  unite : ∀{n}{b : 𝕓 n} → (𝟙 × b) ⇌ b
  uniti : ∀{n}{b : 𝕓 n} → b ⇌ (𝟙 × b)
  distrib : ∀{n}{b₁ b₂ b₃ : 𝕓 n} → ((b₁ + b₂) × b₃) ⇌ ((b₁ × b₃) + (b₂ × b₃))
  factor : ∀{n}{b₁ b₂ b₃ : 𝕓 n} → ((b₁ × b₃) + (b₂ × b₃)) ⇌ ((b₁ + b₂) × b₃)
  id : ∀{n}{b : 𝕓 n} → b ⇌ b
  _+_ : ∀{n}{b₁ b₂ b₃ b₄ : 𝕓 n}
        → b₁ ⇌ b₂
        → b₃ ⇌ b₄
        ----------------
        → (b₁ + b₃) ⇌ (b₂ + b₄)
  _×_ : ∀{n}{b₁ b₂ b₃ b₄ : 𝕓 n}
        → b₁ ⇌ b₂
        → b₃ ⇌ b₄
        ----------------
        → (b₁ × b₃) ⇌ (b₂ × b₄)
  _>_ : ∀{n}{b₁ b₂ b₃ : 𝕓 n}
        → b₁ ⇌ b₂
        → b₂ ⇌ b₃
        ----------------
        → b₁ ⇌ b₃
  trace : ∀{n}{b₁ b₂ b₃ : 𝕓 n}
        → (b₁ + b₂) ⇌ (b₁ + b₃)
        ----------------------
        → b₂ ⇌ b₃

_[_]ᶠ : {n : ℕ}{b b' : 𝕓 n} → b ⇌ b' → val n b → val n b'
-- _[_]ᵇ : {n : ℕ}{b b' : 𝕓 n} → b ⇌ b' → val n b' → val n b

{-# TERMINATING #-}
loop : {n : ℕ}{b₁ b₂ b₃ : 𝕓 n} → (b₁ + b₂) ⇌ (b₁ + b₃) → val n (b₁ + b₃) → val n b₃
loop c (left v) = loop c (c [ left v ]ᶠ)
loop c (right v) = v

{-
{-# TERMINATING #-}
loopᵇ : {n : ℕ}{b₁ b₂ b₃ : 𝕓 n} → (b₁ + b₂) ⇌ (b₁ + b₃) → val n (b₁ + b₂) → val n b₂
loopᵇ c (left v) = loopᵇ c (c [ left v ]ᵇ)
loopᵇ c (right v) = v
-}

swap⁺ [ left v ]ᶠ = right v
swap⁺ [ right v ]ᶠ = left v
id [ v ]ᶠ = v
swapˣ [ ([ v₁ , v₂ ]) ]ᶠ = [ v₂ , v₁ ]
assocl⁺ [ left v₁ ]ᶠ = left (left v₁)
assocl⁺ [ right (left v₂) ]ᶠ = left (right v₂)
assocl⁺ [ right (right v₃) ]ᶠ = right v₃
assocr⁺ [ left (left v₁) ]ᶠ = left v₁
assocr⁺ [ left (right v₂) ]ᶠ = right (left v₂)
assocr⁺ [ right v₃ ]ᶠ = right (right v₃)
fold [ v ]ᶠ = ⟨ v ⟩
unfold [ (⟨ v ⟩) ]ᶠ = v
unite [ ([ [] , v ]) ]ᶠ = v
uniti [ v ]ᶠ = [ [] , v ]
assoclˣ [ ([ v₁ , [ v₂ , v₃ ] ]) ]ᶠ = [ [ v₁ , v₂ ] , v₃ ]
assocrˣ [ ([ [ v₁ , v₂ ] , v₃ ]) ]ᶠ = [ v₁ , [ v₂ , v₃ ] ]
distrib [ ([ left v₁ , v₃ ]) ]ᶠ = left ([ v₁ , v₃ ])
distrib [ ([ right v₂ , v₃ ]) ]ᶠ = right ([ v₂ , v₃ ])
factor [ left ([ v₁ , v₃ ]) ]ᶠ = [ left v₁ , v₃ ]
factor [ right ([ v₂ , v₃ ]) ]ᶠ = [ right v₂ , v₃ ]
(c₁ + c₂) [ left v₁ ]ᶠ = left (c₁ [ v₁ ]ᶠ)
(c₁ + c₂) [ right v₂ ]ᶠ = right (c₂ [ v₂ ]ᶠ)
(c₁ × c₂) [ ([ v₁ , v₂ ]) ]ᶠ = [ (c₁ [ v₁ ]ᶠ) , (c₂ [ v₂ ]ᶠ) ]
(c₁ > c₂) [ v ]ᶠ = c₂ [ (c₁ [ v ]ᶠ) ]ᶠ
(trace c) [ v ]ᶠ = loop c (c [ right v ]ᶠ)

--(trace c) [ v ]ᶠ = (c > (loop c)) [ right v ]ᶠ
--(loop c) [ left v ]ᶠ = (c > (loop c)) [ right v ]ᶠ
--(loop c) [ right v ]ᶠ = v

_† : {n : ℕ}{b b' : 𝕓 n} → b ⇌ b' → b' ⇌ b
swap⁺ † = swap⁺
assoclˣ † = assocrˣ
assocrˣ † = assoclˣ
assocl⁺ † = assocr⁺
assocr⁺ † = assocl⁺
distrib † = factor
factor † = distrib
unite † = uniti
uniti † = unite
fold † = unfold
unfold † = fold
id † = id
swapˣ † = swapˣ
(c₁ + c₂)† = (c₁ †) + (c₂ †)
(c₁ × c₂)† = (c₁ †) × (c₂ †)
(c₁ > c₂)† = (c₂ †) > (c₁ †)
(trace c)† = trace (c †)

-- INTRODUCING A POSTULATE - IT IS DIFFICULT TO FORMALISE THE LOOP PROOF - WE NEED TO INTRODUCE A LOOP COUNT
postulate
  loop-lemma : {n : ℕ}{b₁ b₂ b₃ : 𝕓 n} → (c : (b₁ + b₂) ⇌ (b₁ + b₃)) → (v : val n b₂) → loop (c †) ((c †) [ right (loop c (c [ right v ]ᶠ)) ]ᶠ) ≡ v

--loop-lemma1 : {n : ℕ}{b₁ b₂ b₃ : 𝕓 n} → (c : (b₁ + b₂) ⇌ (b₁ + b₃)) → (v : val n b₂) → loop (c †) ((c †) [ right (loop c (c [ right v ]ᶠ)) ]ᶠ) ≡ v
Π-rev-proof : {n : ℕ}{b b' : 𝕓 n}(c : b ⇌ b')(v : val n b) → (c †) [ c [ v ]ᶠ ]ᶠ ≡ v

--loop-lemma1 c v with (c [ (right v) ]ᶠ) | inspect (_[_]ᶠ c) (right v)
--...                 | (right v') | [ pf ] rewrite sym pf | (Π-rev-proof c (right v)) = refl
--...                 | (left v') | [ pf ] = {!!}

Π-rev-proof swap⁺ (left v) = refl
Π-rev-proof swap⁺ (right v) = refl
Π-rev-proof swapˣ ([ v₁ , v₂ ]) = refl
Π-rev-proof assocl⁺ (left v₁) = refl
Π-rev-proof assocl⁺ (right (left v₂)) = refl
Π-rev-proof assocl⁺ (right (right v₃)) = refl
Π-rev-proof assocr⁺ (left (left v₁)) = refl
Π-rev-proof assocr⁺ (left (right v₂)) = refl
Π-rev-proof assocr⁺ (right v₃) = refl
Π-rev-proof unite ([ [] , v ]) = refl
Π-rev-proof uniti v = refl
Π-rev-proof assoclˣ ([ v₁ , [ v₂ , v₃ ] ]) = refl
Π-rev-proof assocrˣ ([ [ v₁ , v₂ ] , v₃ ]) = refl
Π-rev-proof distrib ([ left v₁ , v₃ ]) = refl
Π-rev-proof distrib ([ right v₂ , v₃ ]) = refl
Π-rev-proof factor (left ([ v₁ , v₃ ])) = refl
Π-rev-proof factor (right ([ v₂ , v₃ ])) = refl
Π-rev-proof id v = refl
Π-rev-proof (c₁ + c₂) (left v) = cong left (Π-rev-proof c₁ v)
Π-rev-proof (c₁ + c₂) (right v₂) = cong right (Π-rev-proof c₂ v₂)
Π-rev-proof (c₁ × c₂) ([ v₁ , v₂ ]) rewrite (Π-rev-proof c₁ v₁) | (Π-rev-proof c₂ v₂) = refl
Π-rev-proof (c₁ > c₂) v = trans (cong ((c₁ †) [_]ᶠ) (Π-rev-proof c₂ (c₁ [ v ]ᶠ))) (Π-rev-proof c₁ v)
Π-rev-proof fold v = refl
Π-rev-proof unfold (⟨ v ⟩) = refl
Π-rev-proof (trace c) v = loop-lemma c v
--Π-rev-proof (trace c) v with (c [ (right v) ]ᶠ) | inspect (_[_]ᶠ c) (right v)
--...                 | (right v') | [ pf ] rewrite sym pf | (Π-rev-proof c (right v)) = refl
--...                 | (left v') | [ pf ] = loop-lemma c v

-- Some basic examples
bool : 𝕓 0
bool = 𝟙 + 𝟙

nat : 𝕓 0
nat = μ (𝟙 + (ref zero))

-- Function to encode arbitrary natural numbers
encode : ℕ → val 0 nat
encode zero = fold [ left [] ]ᶠ
encode (suc n) = fold [ right (encode n) ]ᶠ

test : val 0 nat
test = encode 49

not : bool ⇌ bool
not = swap⁺

c : ((nat × (nat × bool)) + (𝟙 × (nat × bool))) ⇌ ((nat × (nat × bool)) + (𝟙 × (nat × bool)))
c = factor > (((swap⁺ > fold) × id) > ((assoclˣ > ((swapˣ × id) > assocrˣ)) > (((unfold > swap⁺) × id) > (distrib > ((assoclˣ > ((swapˣ × not) > assocrˣ)) + id)))))

--d : (𝟙 × (nat × bool)) ⇌ (𝟙 × (nat × bool))
--d = trace c

c-func : ∀{b : 𝕓 0} → b ⇌ b → ((nat × (nat × b)) + (𝟙 × (nat × b))) ⇌ ((nat × (nat × b)) + (𝟙 × (nat × b)))
c-func x = factor > (((swap⁺ > fold) × id) > ((assoclˣ > ((swapˣ × id) > assocrˣ)) > (((unfold > swap⁺) × id) > (distrib > ((assoclˣ > ((swapˣ × x) > assocrˣ)) + id)))))

d : (𝟙 × (nat × bool)) ⇌ (𝟙 × (nat × bool))
d = trace c

e : (nat × bool) ⇌ (nat × bool)
e = ((uniti × id) > assocrˣ) > (d > (assoclˣ > (unite × id)))

e-func : ∀{b : 𝕓 0} → b ⇌ b → (nat × b) ⇌ (nat × b)
e-func x = ((uniti × id) > assocrˣ) > ((trace (c-func x)) > (assoclˣ > (unite × id)))

e-res : val 0 (nat × bool)
e-res = e [ ([ test , (left []) ]) ]ᶠ

unfold-for-nat : nat ⇌ (𝟙 + nat)
unfold-for-nat = unfold

--c : ∀{n : ℕ}{b : 𝕓 n} → (nat + b) ⇌ (nat + (𝟙 + b))
--c = ((unfold-for-nat > swap⁺) + id) > assocr⁺

just : {b : 𝕓 0} → b ⇌ (𝟙 + b)
just = trace (((unfold-for-nat > swap⁺) + id) > assocr⁺)

add1 : nat ⇌ nat
add1 = just > fold

add : (nat × nat) ⇌ (nat × nat)
add = e-func add1

sub : (nat × nat) ⇌ (nat × nat)
sub = add †

decode : val 0 nat → ℕ
decode ⟨ (left []) ⟩ = 0
decode ⟨ (right x) ⟩ = suc (decode x)

add-res : val 0 (nat × nat)
add-res = add [ ([ (encode 35) , (encode 47) ]) ]ᶠ

sub-res : val 0 (nat × nat)
sub-res = sub [ add-res ]ᶠ

snd : val 0 (nat × nat) → val 0 nat
snd [ x , y ] = y

add-val : ℕ
add-val = decode (snd(add-res))

sub-val : ℕ
sub-val = decode (snd(sub-res))

sub1 : nat ⇌ nat
sub1 = add1 †

testAdd : val 0 nat
testAdd = sub1 [(encode 7)]ᶠ

introR : 𝟙 ⇌ bool
introR = just

introF : 𝟙 ⇌ bool
introF = just > not

{-# TERMINATING #-}
φ : (b : 𝕓 0) → val 0 b
φ 𝟙 = []
φ (b₁ × b₂) = [ φ b₁ , φ b₂ ]
φ (b₁ + b₂) = left (φ b₁)
φ (μ b) = ⟨ (φ (_[_] b (μ b))) ⟩

{-# TERMINATING #-}
createConst : {b : 𝕓 0} → val 0 b → 𝟙 ⇌ b
createConst [] = id
createConst [ v₁ , v₂ ] = uniti > ((createConst v₁) × (createConst v₂))
createConst {b = b₁ + b₂} (left v) = introF > ((createConst v) + (createConst (φ(b₂))))
createConst {b = b₁ + b₂} (right v) = introR > ((createConst (φ(b₁))) + (createConst v))
createConst (⟨ v ⟩) = (createConst v) > fold

-- Test that constant is actually created
testCreate : val 0 nat
testCreate = (createConst (encode 7)) [ [] ]ᶠ

-- The type of a list is not allowed to recursively reference that same type
_List : 𝕓 0 → 𝕓 0
b List = μ (𝟙 + ((inc b) × (ref zero)))

--unfold-for-lists : {b : 𝕓 0} → (b List) ⇌ (𝟙 + (b List))
--unfold-for-lists = unfold

--addList : {b : 𝕓 0} → (b × (b List)) ⇌ (b List)
--addList = just > fold

