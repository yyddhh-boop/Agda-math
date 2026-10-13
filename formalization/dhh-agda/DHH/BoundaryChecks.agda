{-# OPTIONS --cubical --safe #-}

module DHH.BoundaryChecks where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; false; true; false≢true; true≢false)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Relation.Nullary using (Discrete; yes; no; Discrete→isSet)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.FiniteInterval using (UnitInterval)
open import DHH.Cellular2 using (GraphSquare; v00; v10; v01; v11; left)

-- The cartesian graph product allows only one coordinate to change.
-- A diagonal from (false,false) to (true,true) is therefore NOT an edge.
no-diagonal-edge : Adj (UnitInterval BOX UnitInterval)
                       (false , false) (true , true) → ⊥
no-diagonal-edge = PT.rec isProp⊥ λ where
  (inl (p , e)) → false≢true p
  (inr (e , p)) → false≢true p

diagonal : Bool → Bool × Bool
diagonal x = x , x

-- This rejects every proposed graph map with this vertex function,
-- rather than merely failing to provide one particular edge proof.
diagonal-not-hom : (f : Hom UnitInterval (UnitInterval BOX UnitInterval))
                 → ((x : Bool) → onVertices f x ≡ diagonal x) → ⊥
diagonal-not-hom f p = no-diagonal-edge
  (subst2 (Adj (UnitInterval BOX UnitInterval)) (p false) (p true)
    (preserves f {x = false} {y = true} tt))

-- A separate finite graph: the reflexive path 0--1--2.
data Three : Type where
  zero one two : Three

marksOne : Three → Bool
marksOne zero = false
marksOne one = true
marksOne two = false

marksTwo : Three → Bool
marksTwo zero = false
marksTwo one = false
marksTwo two = true

discreteThree : Discrete Three
discreteThree zero zero = yes refl
discreteThree zero one = no (λ p → false≢true (cong marksOne p))
discreteThree zero two = no (λ p → false≢true (cong marksTwo p))
discreteThree one zero = no (λ p → true≢false (cong marksOne p))
discreteThree one one = yes refl
discreteThree one two = no (λ p → true≢false (cong marksOne p))
discreteThree two zero = no (λ p → true≢false (cong marksTwo p))
discreteThree two one = no (λ p → true≢false (cong marksTwo p))
discreteThree two two = yes refl

PathAdj : Three → Three → Type
PathAdj zero zero = Unit
PathAdj zero one = Unit
PathAdj zero two = ⊥
PathAdj one zero = Unit
PathAdj one one = Unit
PathAdj one two = Unit
PathAdj two zero = ⊥
PathAdj two one = Unit
PathAdj two two = Unit

pathAdjProp : (x y : Three) → isProp (PathAdj x y)
pathAdjProp zero zero = isPropUnit
pathAdjProp zero one = isPropUnit
pathAdjProp zero two = isProp⊥
pathAdjProp one zero = isPropUnit
pathAdjProp one one = isPropUnit
pathAdjProp one two = isPropUnit
pathAdjProp two zero = isProp⊥
pathAdjProp two one = isPropUnit
pathAdjProp two two = isPropUnit

pathAdjRefl : (x : Three) → PathAdj x x
pathAdjRefl zero = tt
pathAdjRefl one = tt
pathAdjRefl two = tt

pathAdjSym : {x y : Three} → PathAdj x y → PathAdj y x
pathAdjSym {zero} {zero} _ = tt
pathAdjSym {zero} {one} _ = tt
pathAdjSym {zero} {two} ()
pathAdjSym {one} {zero} _ = tt
pathAdjSym {one} {one} _ = tt
pathAdjSym {one} {two} _ = tt
pathAdjSym {two} {zero} ()
pathAdjSym {two} {one} _ = tt
pathAdjSym {two} {two} _ = tt

ThreePath : Graph ℓ-zero
Vertex ThreePath = Three
vertex-isSet ThreePath = Discrete→isSet discreteThree
Adj ThreePath = PathAdj
adj-isProp ThreePath = pathAdjProp
adj-refl ThreePath = pathAdjRefl
adj-sym ThreePath = pathAdjSym

-- The three specified sides are individually legal:
--          2 ------- 2
--          .         |
--          .         |
--          0 ------- 1
-- The missing side would have to connect 0 to 2, which is impossible.
bottom-is-legal : Adj ThreePath zero one
bottom-is-legal = tt

right-is-legal : Adj ThreePath one two
right-is-legal = tt

top-is-legal : Adj ThreePath two two
top-is-legal = tt

missing-left-is-impossible : Adj ThreePath zero two → ⊥
missing-left-is-impossible e = e

-- Even allowing path-equal corner labels cannot produce a GraphSquare.
-- This is an elementary extension obstruction.  We do NOT define a
-- category of horns here or assert a theorem about the full nerve.
no-square-with-these-corners : (s : GraphSquare ThreePath)
                             → v00 s ≡ zero
                             → v10 s ≡ one
                             → v01 s ≡ two
                             → v11 s ≡ two
                             → ⊥
no-square-with-these-corners s p00 p10 p01 p11 =
  missing-left-is-impossible (subst2 PathAdj p00 p01 (left s))
