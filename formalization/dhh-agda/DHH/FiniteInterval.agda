{-# OPTIONS --cubical --safe #-}

module DHH.FiniteInterval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Data.Bool using (Bool; false; true; isSetBool)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import DHH.Graph

-- This is a finite graph with two vertices, not Agda's primitive interval I.
UnitInterval : Graph ℓ-zero
Vertex UnitInterval = Bool
vertex-isSet UnitInterval = isSetBool
Adj UnitInterval _ _ = Unit
adj-isProp UnitInterval _ _ = isPropUnit
adj-refl UnitInterval _ = tt
adj-sym UnitInterval _ = tt

Four : Type
Four = Bool × Bool

pattern p0 = false , false
pattern p1 = false , true
pattern p2 = true , false
pattern p3 = true , true

-- The four vertices are numbered 0,1,2,3, and only consecutive
-- distinct vertices are adjacent.  All four loops are present.
I3Adj : Four → Four → Type
I3Adj p0 p0 = Unit
I3Adj p0 p1 = Unit
I3Adj p0 p2 = ⊥
I3Adj p0 p3 = ⊥
I3Adj p1 p0 = Unit
I3Adj p1 p1 = Unit
I3Adj p1 p2 = Unit
I3Adj p1 p3 = ⊥
I3Adj p2 p0 = ⊥
I3Adj p2 p1 = Unit
I3Adj p2 p2 = Unit
I3Adj p2 p3 = Unit
I3Adj p3 p0 = ⊥
I3Adj p3 p1 = ⊥
I3Adj p3 p2 = Unit
I3Adj p3 p3 = Unit

I3AdjProp : (x y : Four) → isProp (I3Adj x y)
I3AdjProp p0 p0 = isPropUnit
I3AdjProp p0 p1 = isPropUnit
I3AdjProp p0 p2 = isProp⊥
I3AdjProp p0 p3 = isProp⊥
I3AdjProp p1 p0 = isPropUnit
I3AdjProp p1 p1 = isPropUnit
I3AdjProp p1 p2 = isPropUnit
I3AdjProp p1 p3 = isProp⊥
I3AdjProp p2 p0 = isProp⊥
I3AdjProp p2 p1 = isPropUnit
I3AdjProp p2 p2 = isPropUnit
I3AdjProp p2 p3 = isPropUnit
I3AdjProp p3 p0 = isProp⊥
I3AdjProp p3 p1 = isProp⊥
I3AdjProp p3 p2 = isPropUnit
I3AdjProp p3 p3 = isPropUnit

I3AdjRefl : (x : Four) → I3Adj x x
I3AdjRefl p0 = tt
I3AdjRefl p1 = tt
I3AdjRefl p2 = tt
I3AdjRefl p3 = tt

I3AdjSym : {x y : Four} → I3Adj x y → I3Adj y x
I3AdjSym {p0} {p0} _ = tt
I3AdjSym {p0} {p1} _ = tt
I3AdjSym {p0} {p2} ()
I3AdjSym {p0} {p3} ()
I3AdjSym {p1} {p0} _ = tt
I3AdjSym {p1} {p1} _ = tt
I3AdjSym {p1} {p2} _ = tt
I3AdjSym {p1} {p3} ()
I3AdjSym {p2} {p0} ()
I3AdjSym {p2} {p1} _ = tt
I3AdjSym {p2} {p2} _ = tt
I3AdjSym {p2} {p3} _ = tt
I3AdjSym {p3} {p0} ()
I3AdjSym {p3} {p1} ()
I3AdjSym {p3} {p2} _ = tt
I3AdjSym {p3} {p3} _ = tt

I3 : Graph ℓ-zero
Vertex I3 = Four
vertex-isSet I3 = isSet× isSetBool isSetBool
Adj I3 = I3Adj
adj-isProp I3 = I3AdjProp
adj-refl I3 = I3AdjRefl
adj-sym I3 = I3AdjSym

path3 : {ℓ : Level} (G : Graph ℓ) (x0 x1 x2 x3 : Vertex G)
        → Adj G x0 x1 → Adj G x1 x2 → Adj G x2 x3 → Hom I3 G
path3 G x0 x1 x2 x3 e01 e12 e23 = record
  { onVertices = run
  ; preserves = respect
  }
  where
  run : Four → Vertex G
  run p0 = x0
  run p1 = x1
  run p2 = x2
  run p3 = x3
  respect : {x y : Four} → I3Adj x y → Adj G (run x) (run y)
  respect {p0} {p0} _ = adj-refl G _
  respect {p0} {p1} _ = e01
  respect {p0} {p2} ()
  respect {p0} {p3} ()
  respect {p1} {p0} _ = adj-sym G e01
  respect {p1} {p1} _ = adj-refl G _
  respect {p1} {p2} _ = e12
  respect {p1} {p3} ()
  respect {p2} {p0} ()
  respect {p2} {p1} _ = adj-sym G e12
  respect {p2} {p2} _ = adj-refl G _
  respect {p2} {p3} _ = e23
  respect {p3} {p0} ()
  respect {p3} {p1} ()
  respect {p3} {p2} _ = adj-sym G e23
  respect {p3} {p3} _ = adj-refl G _
