{-# OPTIONS --cubical --safe #-}

module DHH.Cellular2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path using (Square→compPath)
open import DHH.Graph

private
  variable
    ℓ ℓ' : Level

-- Four vertices together with the four required adjacency witnesses.
-- A diagonal adjacency is neither required nor inserted.
record GraphSquare (G : Graph ℓ) : Type ℓ where
  field
    v00 v10 v01 v11 : Vertex G
    bottom : Adj G v00 v10
    top    : Adj G v01 v11
    left   : Adj G v00 v01
    right  : Adj G v10 v11

open GraphSquare public

-- An auxiliary free point/edge/square presentation, NOT the full |N₁G|.
-- In particular we have not identified all degenerate cubes, nor added
-- the higher cells of N₁G.  The type must not be truncated to a set.
data Cell₂ (G : Graph ℓ) : Type ℓ where
  point : Vertex G → Cell₂ G
  edge  : {x y : Vertex G} → Adj G x y → point x ≡ point y
  tile  : (s : GraphSquare G)
        → Square (edge (bottom s)) (edge (top s))
                 (edge (left s)) (edge (right s))

-- The important consequence of a square: its two routes have the same
-- endpoints and are equal AS PATHS.  This is a two-dimensional equality.
routesAgree : {G : Graph ℓ} (s : GraphSquare G)
            → edge (bottom s) ∙ edge (right s)
            ≡ edge (left s) ∙ edge (top s)
routesAgree s = sym (Square→compPath (tile s))

-- An interpretation states exactly the boundary data needed to extend
-- to Cell₂.  Giving only four points and four edges is insufficient:
-- a specified square must also be supplied in the target type.
record Interpretation (G : Graph ℓ) (A : Type ℓ')
       : Type (ℓ-max ℓ ℓ') where
  field
    points : Vertex G → A
    edges  : {x y : Vertex G} → Adj G x y → points x ≡ points y
    squares : (s : GraphSquare G)
            → Square (edges (bottom s)) (edges (top s))
                     (edges (left s)) (edges (right s))

open Interpretation public

interpret : {G : Graph ℓ} {A : Type ℓ'}
          → Interpretation G A → Cell₂ G → A
interpret t (point x) = points t x
interpret t (edge e i) = edges t e i
interpret t (tile s i j) = squares t s i j

pointComputation : {G : Graph ℓ} {A : Type ℓ'}
                 → (t : Interpretation G A) (x : Vertex G)
                 → interpret t (point x) ≡ points t x
pointComputation t x = refl

edgeComputation : {G : Graph ℓ} {A : Type ℓ'}
                → (t : Interpretation G A) {x y : Vertex G}
                → (e : Adj G x y)
                → cong (interpret t) (edge e) ≡ edges t e
edgeComputation t e = refl

squareComputation : {G : Graph ℓ} {A : Type ℓ'}
                  → (t : Interpretation G A) (s : GraphSquare G)
                  → (λ i j → interpret t (tile s i j)) ≡ squares t s
squareComputation t s = refl
