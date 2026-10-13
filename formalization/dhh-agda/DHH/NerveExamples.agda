{-# OPTIONS --cubical --safe #-}

module DHH.NerveExamples where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Data.Bool using (false; true)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Categories.Category.Base using (CatIso)
open import DHH.Graph
open import DHH.Cubes using (Cube; PointGraph)
open import DHH.Homotopy
open import DHH.HomotopyCategory
open import DHH.Cellular2
open import DHH.CubicalBridge
open import DHH.Examples using (C4; a; b; c; d; c4Square; c4-contracts)
import DHH.BoundaryChecks as B

-- The earlier picture really supplies an element of the raw nerve N₁.
c4NerveSquare : Cube C4 2
c4NerveSquare = squareToCube c4Square

c4-corner-00 : onVertices c4NerveSquare (false , (false , tt)) ≡ a
c4-corner-00 = refl

c4-corner-10 : onVertices c4NerveSquare (true , (false , tt)) ≡ b
c4-corner-10 = refl

c4-corner-01 : onVertices c4NerveSquare (false , (true , tt)) ≡ d
c4-corner-01 = refl

c4-corner-11 : onVertices c4NerveSquare (true , (true , tt)) ≡ c
c4-corner-11 = refl

c4-square-roundtrip : cubeToSquare c4NerveSquare ≡ c4Square
c4-square-roundtrip = squareRoundTrip c4Square

c4-nerve-routes :
  edge (bottom (cubeToSquare c4NerveSquare)) ∙ edge (right (cubeToSquare c4NerveSquare))
  ≡ edge (left (cubeToSquare c4NerveSquare)) ∙ edge (top (cubeToSquare c4NerveSquare))
c4-nerve-routes = cubeRoutesAgree c4NerveSquare

-- Transfer the checked obstruction to the exact Q₂-mapping definition.
-- No generic horn object or theorem about the full Kan nerve is assumed.
no-nerve-square-with-these-corners : (s : Cube B.ThreePath 2)
  → onVertices s (false , (false , tt)) ≡ B.zero
  → onVertices s (true  , (false , tt)) ≡ B.one
  → onVertices s (false , (true  , tt)) ≡ B.two
  → onVertices s (true  , (true  , tt)) ≡ B.two
  → ⊥
no-nerve-square-with-these-corners s =
  B.no-square-with-these-corners (cubeToSquare s)

-- A complete, concrete Malle-style graph homotopy equivalence.  The
-- result stated below is in the ordinary homotopy category HoGraph.
-- No realization or infinity-localization comparison is assumed.
c4PointEquivalence : GraphHomotopyEquivalence C4 PointGraph
GraphHomotopyEquivalence.forward c4PointEquivalence = constantHom PointGraph tt
GraphHomotopyEquivalence.backward c4PointEquivalence = constantHom C4 a
GraphHomotopyEquivalence.retract c4PointEquivalence =
  chain-sym {G = C4} {H = C4} c4-contracts
GraphHomotopyEquivalence.section c4PointEquivalence =
  next (λ _ → tt) (stop (idHom PointGraph))

c4IsoPoint : CatIso (HoGraph ℓ-zero) C4 PointGraph
c4IsoPoint = graphEquivalenceToIso c4PointEquivalence
