\begin{code}

{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Translations.Sigma where

open import Agda.Primitive

\end{code}
%<*exist>

\begin{code}
record Σ {a b} (X : Set a) (P : X → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    x : X
    pₓ : P x
\end{code}
%</exist>
\begin{code}

\end{code}
%<*type>

\begin{code}
data GenericType : Set where
\end{code}
%</type>
\begin{code}

\end{code}
%<*refl>
\begin{code}
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
\end{code}
%</refl>
\begin{code}

open Σ public

infixr 4 _,_

{-# BUILTIN SIGMA Σ #-}
\end{code}
