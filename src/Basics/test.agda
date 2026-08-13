{-# OPTIONS --cubical --guardedness #-}

module Basics.test where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥ using (⊥)

------------------------------------------------------------------------
-- Some elementary exercises in Agda
------------------------------------------------------------------------

-- Question: How does a particular mathematical proposition form a Type?
-- We consider several examples.

-----------------------------------------------------------------------------------------------------
-- Example 1: x ≤ y, where x y : ℕ.
-- The proposition x ≤ y is a type whose elements are all proofs of x ≤ y.
-- If x ≤ y is true, then the type x ≤ y is inhabited; otherwise, it is empty.
-----------------------------------------------------------------------------------------------------

data _≤_ : ℕ → ℕ → Type where
  z≤s : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

data _≥_ : ℕ → ℕ → Type where
  s≥z : ∀ {n : ℕ} → n ≥ zero
  s≥s : ∀ {m n : ℕ} → m ≥ n → suc m ≥ suc n

------------------------------------------------------------------------
-- Example 2: Σ-types, divisibility, and primality
------------------------------------------------------------------------

-- We now introduce Σ-types, use them to express divisibility, and then
-- define primality by combining a lower bound with a condition on all
-- divisors. Finally, we describe the data contained in several concrete
-- inhabitants of IsPrime n.
--
-- We begin with the general form of a Σ-type.
-- Their general form is:
--
--   Σ : (A : Type) → (A → Type) → Type
--
-- written as:
--
--   Σ[ a ∈ A ] B a
--
-- A Σ-type is a dependent pair type. Its elements are pairs (a , b),
-- where a : A and b : B a.
--
-- For example, the following is an element of Σ[ n ∈ ℕ ] n ≤ 4.

eg-3≤4 : Σ[ n ∈ ℕ ] n ≤ 4
eg-3≤4 = 3 , s≤s (s≤s (s≤s z≤s))

------------------------------------------------------------------------
-- Syntax note: ␠ below denotes a space. Omitting these required spaces
-- causes a parsing error.
--
--   Σ[␠n␠∈␠ℕ␠]␠n␠≤␠4
--   eg-3≤4 = 3␠,␠s≤s (s≤s (s≤s z≤s))
--
-- Spaces in many other positions appear to be optional.
------------------------------------------------------------------------

Division : ℕ → ℕ → Type
Division d n = Σ[ k ∈ ℕ ] k · d ≡ n

IsPrime : ℕ → Type
IsPrime n =
  (n ≥ 2)
  × ((d : ℕ) → Division d n → (d ≡ 1) ⊎ (d ≡ n))

------------------------------------------------------------------------
-- A concrete inhabitant of IsPrime 5
------------------------------------------------------------------------

private
  pred⁵ : ℕ → ℕ
  pred⁵ n = predℕ (predℕ (predℕ (predℕ (predℕ n))))

  -- By inspecting the possible values of d and its multiplication witness,
  -- we prove that every divisor of 5 is either 1 or 5.
  divisor-of-5 : (d : ℕ) → Division d 5 → (d ≡ 1) ⊎ (d ≡ 5)
  divisor-of-5 zero (k , p) = ⊥.rec (znots (0≡m·0 k ∙ p))
  divisor-of-5 (suc zero) _ = inl refl
  divisor-of-5 2 (zero , p) = ⊥.rec (znots p)
  divisor-of-5 2 (suc zero , p) =
    ⊥.rec (znots (cong predℕ (cong predℕ p)))
  divisor-of-5 2 (suc (suc zero) , p) =
    ⊥.rec (znots (cong predℕ (cong predℕ (cong predℕ (cong predℕ p)))))
  divisor-of-5 2 (suc (suc (suc k)) , p) = ⊥.rec (snotz (cong pred⁵ p))
  divisor-of-5 3 (zero , p) = ⊥.rec (znots p)
  divisor-of-5 3 (suc zero , p) =
    ⊥.rec (znots (cong predℕ (cong predℕ (cong predℕ p))))
  divisor-of-5 3 (suc (suc k) , p) = ⊥.rec (snotz (cong pred⁵ p))
  divisor-of-5 4 (zero , p) = ⊥.rec (znots p)
  divisor-of-5 4 (suc zero , p) =
    ⊥.rec (znots (cong predℕ (cong predℕ (cong predℕ (cong predℕ p)))))
  divisor-of-5 4 (suc (suc k) , p) = ⊥.rec (snotz (cong pred⁵ p))
  divisor-of-5 5 _ = inr refl
  divisor-of-5 (suc (suc (suc (suc (suc (suc d)))))) (zero , p) =
    ⊥.rec (znots p)
  divisor-of-5 (suc (suc (suc (suc (suc (suc d)))))) (suc k , p) =
    ⊥.rec (snotz (cong pred⁵ p))

prime-5 : IsPrime 5
prime-5 = s≥s (s≥s s≥z) , divisor-of-5
