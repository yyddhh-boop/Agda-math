{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.StagePadding where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-suc; +-comm)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.Int using (ℤ; sucℤ)
open import Cubical.Data.Bool using (Bool; false; true; not)
open import Cubical.Data.Sigma
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.StableNerve.Interval
open import DHH.StableNerve.Grid using (Grid)
open import DHH.StableNerve.IntegerInterval using (IntegerGrid)
open import DHH.StableNerve.IntegerClamp using (clamp)
open import DHH.StableNerve.CenteredInterval
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Padding
open import DHH.StableNerve.StageArithmetic using (Later; fromLe; lengthLater; laterLe)
open import DHH.StableNerve.CommonStage
open import DHH.StableNerve.Colimit
open import DHH.StableNerve.IntegerStable

-- The input length is m=suc k.  The output stage has length 3m, and
-- this parenthesization makes suc(tripleStage k)=m+(m+m) definitional.
tripleStage : ℕ → ℕ
tripleStage k = k + (suc k + suc k)

tripleBound : (k : ℕ) → k ≤ tripleStage k
tripleBound k = (suc k + suc k) , +-comm (suc k + suc k) k

-- This is the actual finite path in the original alternating sequence.
tripleLater : (k : ℕ) → Later k (tripleStage k)
tripleLater k = fromLe (tripleBound k)

-- Every pair of consecutive transitions grows the centered offset once,
-- independently of whether its first transition adds left or right padding.
private
  shift-pair : (b : Bool) (a : ℕ)
    → shiftNext (not b) (shiftNext b a) ≡ suc a
  shift-pair true a = refl
  shift-pair false a = refl

offset-pair : (k : ℕ) → offset (suc (suc k)) ≡ suc (offset k)
offset-pair k = shift-pair (evenStage k) (offset k)

offset-pairs : (a k : ℕ) → offset (double a + k) ≡ a + offset k
offset-pairs zero k = refl
offset-pairs (suc a) k = offset-pair (double a + k)
  ∙ cong suc (offset-pairs a k)

double-sum : (a : ℕ) → double a ≡ a + a
double-sum zero = refl
double-sum (suc a) = cong (λ b → suc (suc b)) (double-sum a)
  ∙ cong suc (sym (+-suc a a))

triple-offset : (k : ℕ) → offset (tripleStage k) ≡ suc k + offset k
triple-offset k =
  cong offset (sym (+-comm (suc k + suc k) k))
  ∙ cong offset (cong (_+ k) (sym (double-sum (suc k))))
  ∙ offset-pairs (suc k) k

up-sum : (a b : ℕ) (z : ℤ) → up (a + b) z ≡ up a (up b z)
up-sum zero b z = refl
up-sum (suc a) b z = cong sucℤ (up-sum a b z)

-- These identities act on every integer, including points beyond either
-- endpoint.  They follow the padding recursion rather than finite testing.
left-padding-shift : (a m : ℕ) (z : ℤ)
  → onVertices (intervalMap (removeLeftPadding a m))
      (clamp (a + m) (up a z)) ≡ clamp m z
left-padding-shift zero m z = refl
left-padding-shift (suc a) m z =
  cong (onVertices (intervalMap (removeLeftPadding a m)))
    (clamp-left-shift (a + m) (up a z))
  ∙ left-padding-shift a m z

right-padding-integer : (a m : ℕ) (z : ℤ)
  → onVertices (intervalMap (removeRightPadding a m))
      (clamp (a + m) z) ≡ clamp m z
right-padding-integer zero m z = refl
right-padding-integer (suc a) m z =
  cong (onVertices (intervalMap (removeRightPadding a m)))
    (clamp-right (a + m) z)
  ∙ right-padding-integer a m z

middle-shift : (m : ℕ) (z : ℤ)
  → onVertices (intervalMap (middleCollapse m))
      (clamp (m + (m + m)) (up m z)) ≡ clamp m z
middle-shift m z =
  cong (onVertices (intervalMap (removeRightPadding m m)))
    (left-padding-shift m (m + m) z)
  ∙ right-padding-integer m m z

middle-shifted-clamp : (m a : ℕ) (z : ℤ)
  → onVertices (intervalMap (middleCollapse m))
      (onVertices (shiftedClamp (m + a) (m + (m + m))) z)
    ≡ onVertices (shiftedClamp a m) z
middle-shifted-clamp m a z =
  cong (λ w → onVertices (intervalMap (middleCollapse m))
    (clamp (m + (m + m)) w)) (up-sum m a z)
  ∙ middle-shift m (up a z)

middle-centered-clamp : (k : ℕ) (z : ℤ)
  → onVertices (intervalMap (middleCollapse (suc k)))
      (onVertices (centeredClamp (tripleStage k)) z)
    ≡ onVertices (centeredClamp k) z
middle-centered-clamp k z =
  cong (λ a → onVertices (intervalMap (middleCollapse (suc k)))
    (onVertices (shiftedClamp a (suc (tripleStage k))) z)) (triple-offset k)
  ∙ middle-shifted-clamp (suc k) (offset k) z

middle-centered-grid-point : (k n : ℕ) (x : Vertex (IntegerGrid n))
  → onVertices (middleGrid (suc k) n)
      (onVertices (centeredClampGrid (tripleStage k) n) x)
    ≡ onVertices (centeredClampGrid k n) x
middle-centered-grid-point k zero x = refl
middle-centered-grid-point k (suc n) (z , x) = cong₂ _,_
  (middle-centered-clamp k z) (middle-centered-grid-point k n x)

middle-centered-grid : (k n : ℕ)
  → middleGrid (suc k) n ∘g centeredClampGrid (tripleStage k) n
    ≡ centeredClampGrid k n
middle-centered-grid k n = homExt (middle-centered-grid-point k n)

private variable ℓ : Level
module ForGraph (G : Graph ℓ) where
  module K = CommonStages (Stage G) (stageTransition G)
  module IC = IntegerComparison G

  middle-extension : (k n : ℕ) (c : Hom (Grid (suc k) n) G)
    → centeredExtend (tripleStage k) n (c ∘g middleGrid (suc k) n)
      ≡ centeredExtend k n c
  middle-extension k n c = homExt λ x →
    cong (onVertices c) (middle-centered-grid-point k n x)

  -- Both sides are programs on the same finite grid.  The first follows
  -- the original alternating sequence; the second deletes m layers on
  -- each side.  Injectivity of centered extension proves their equality.
  middle-later-cell : (k n : ℕ) (c : Hom (Grid (suc k) n) G)
    → mapCells (K.laterMap (tripleLater k)) n c
      ≡ c ∘g middleGrid (suc k) n
  middle-later-cell k n c = centeredExtend-injective (tripleStage k) n
    (IC.extension-later (tripleLater k) n c ∙ sym (middle-extension k n c))

  middle-later : (k : ℕ)
    → K.laterMap (tripleLater k) ≡ changeSize (middleCollapse (suc k)) G
  middle-later k = cubicalNaturalExt (middle-later-cell k)

  middle-advance : (k : ℕ)
    → K.advance (tripleBound k) ≡ changeSize (middleCollapse (suc k)) G
  middle-advance = middle-later

  -- The middle-window refinement represents exactly the original stable
  -- cell; this is the cocone identity consumed by the universal filler.
  middle-include : (k : ℕ)
    → changeSize (middleCollapse (suc k)) G ⋆n includeStage G (tripleStage k)
      ≡ includeStage G k
  middle-include k = cubicalNaturalExt λ n c →
    sym (cong (mapCells (includeStage G (tripleStage k)) n) (middle-later-cell k n c))
    ∙ sym (K.point-later (tripleLater k) n c)
