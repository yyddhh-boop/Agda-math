{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.OrdinalLaws where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import DHH.Cubes using (Position; here; there; weakenPosition;
  CoordinatePair; front; under; lower; upper; lowerWide; upperWide)
open import DHH.Simplicial.Ordinal

positionFin : {n : ℕ} → Position n → Fin n
positionFin here = fzero
positionFin (there i) = fsuc (positionFin i)

faceFn : {n : ℕ} → Position (suc n) → Fin n → Fin (suc n)
faceFn i = skip (positionFin i)

degenFn : {n : ℕ} → Position n → Fin (suc n) → Fin n
degenFn i = collapseAny (positionFin i)

faces-law : {n : ℕ} (p : CoordinatePair n) (x : Fin n)
          → faceFn (lowerWide p) (faceFn (upper p) x)
          ≡ faceFn (upperWide p) (faceFn (lower p) x)
faces-law (front j) x = refl
faces-law (under p) fzero = refl
faces-law (under p) (fsuc x) = cong fsuc (faces-law p x)

degens-law : {n : ℕ} (p : CoordinatePair n) (x : Fin (suc (suc (suc n))))
           → degenFn (upper p) (degenFn (lowerWide p) x)
           ≡ degenFn (lower p) (degenFn (upperWide p) x)
degens-law (front here) fzero = refl
degens-law (front here) (fsuc fzero) = refl
degens-law (front here) (fsuc (fsuc x)) = refl
degens-law (front (there j)) fzero = refl
degens-law (front (there j)) (fsuc x) = refl
degens-law (under p) fzero = refl
degens-law (under p) (fsuc x) = cong fsuc (degens-law p x)

same-law : {n : ℕ} (i : Position (suc n)) (x : Fin (suc n))
         → degenFn i (faceFn (weakenPosition i) x) ≡ x
same-law here x = refl
same-law {n = zero} (there ()) x
same-law {n = suc n} (there i) fzero = refl
same-law {n = suc n} (there i) (fsuc x) = cong fsuc (same-law i x)

next-law : {n : ℕ} (i : Position (suc n)) (x : Fin (suc n))
         → degenFn i (faceFn (there i) x) ≡ x
next-law here fzero = refl
next-law here (fsuc x) = refl
next-law {n = zero} (there ()) x
next-law {n = suc n} (there i) fzero = refl
next-law {n = suc n} (there i) (fsuc x) = cong fsuc (next-law i x)

before-law : {n : ℕ} (p : CoordinatePair n) (x : Fin (suc (suc n)))
           → degenFn (upperWide p) (faceFn (weakenPosition (lowerWide p)) x)
           ≡ faceFn (lowerWide p) (degenFn (upper p) x)
before-law (front j) x = refl
before-law (under p) fzero = refl
before-law (under p) (fsuc x) = cong fsuc (before-law p x)

after-law : {n : ℕ} (p : CoordinatePair n) (x : Fin (suc (suc n)))
          → degenFn (lowerWide p) (faceFn (there (upperWide p)) x)
          ≡ faceFn (upperWide p) (degenFn (lower p) x)
after-law (front j) fzero = refl
after-law (front j) (fsuc x) = refl
after-law (under p) fzero = refl
after-law (under p) (fsuc x) = cong fsuc (after-law p x)
