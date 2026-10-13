{-# OPTIONS --cubical --safe #-}

module DHH.StableNerve.TransitionMonomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
open import DHH.Graph
open import DHH.Cubes using (boxHom)
open import DHH.CubicalNerve
open import DHH.StableNerve.Interval
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.StageArithmetic

private variable ℓ : Level

-- Source: Carranza--Kapulkin, arXiv:2202.03516v3, §1 (the l/r
-- interval collapses), Proposition 3.5 (the alternating nerve sequence),
-- and §4, proof of part (2) (its transition maps are inclusions).
-- https://arxiv.org/pdf/2202.03516v3
-- Here the inclusion statement is proved directly, in every dimension:
-- each interval collapse has an explicit graph section, hence its grid
-- power is surjective and precomposition is injective.  No anodyne or
-- topological weak-equivalence statement is supplied by this module.

leftSectionVertex : {m : ℕ} → Fin (suc m) → Fin (suc (suc m))
leftSectionVertex = fsuc

rightSectionVertex : {m : ℕ} → Fin (suc m) → Fin (suc (suc m))
rightSectionVertex fzero = fzero
rightSectionVertex {suc m} (fsuc x) = fsuc (rightSectionVertex {m} x)

rightSection-near : {m : ℕ} {x y : Fin (suc m)}
  → Near x y → Near (rightSectionVertex x) (rightSectionVertex y)
rightSection-near {x = fzero} {y = fzero} e = tt
rightSection-near {suc m} {fzero} {fsuc fzero} e = tt
rightSection-near {suc m} {fzero} {fsuc (fsuc y)} ()
rightSection-near {suc m} {fsuc fzero} {fzero} e = tt
rightSection-near {suc m} {fsuc (fsuc x)} {fzero} ()
rightSection-near {suc m} {fsuc x} {fsuc y} e =
  rightSection-near {m} {x} {y} e

leftSection : (m : ℕ) → Hom (Iₘ m) (Iₘ (suc m))
onVertices (leftSection m) = leftSectionVertex
preserves (leftSection m) {x = x} {y = y} e = e

rightSection : (m : ℕ) → Hom (Iₘ m) (Iₘ (suc m))
onVertices (rightSection m) = rightSectionVertex
preserves (rightSection m) {x = x} {y = y} e =
  rightSection-near {m} {x} {y} e

left-section : (m : ℕ) (x : Fin (suc m))
  → onVertices (leftMap m) (onVertices (leftSection m) x) ≡ x
left-section m x = refl

right-section : (m : ℕ) (x : Fin (suc m))
  → onVertices (rightMap m) (onVertices (rightSection m) x) ≡ x
right-section m fzero = refl
right-section (suc m) (fsuc x) = cong fsuc (right-section m x)

-- These graph sections need not preserve BOTH designated endpoints.
-- Thus they are not IntervalMorphs and do not yield a cubical natural
-- inverse to leftTransition/rightTransition.  They are used only to
-- detect equality of maps by evaluating at preimages of grid vertices.
gridSection : {r s : ℕ} → Hom (Iₘ s) (Iₘ r)
  → (n : ℕ) → Hom (Grid s n) (Grid r n)
gridSection S zero = idHom _
gridSection S (suc n) = boxHom S (gridSection S n)

mapGrid-section-point : {r s : ℕ} (M : IntervalMorph r s)
  (S : Hom (Iₘ s) (Iₘ r))
  (split : (x : Fin (suc s))
    → onVertices (intervalMap M) (onVertices S x) ≡ x)
  (n : ℕ) (x : Vertex (Grid s n))
  → onVertices (mapGrid M n) (onVertices (gridSection S n) x) ≡ x
mapGrid-section-point M S split zero x = refl
mapGrid-section-point M S split (suc n) (a , x) = cong₂ _,_
  (split a) (mapGrid-section-point M S split n x)

mapGrid-section : {r s : ℕ} (M : IntervalMorph r s)
  (S : Hom (Iₘ s) (Iₘ r))
  (split : (x : Fin (suc s))
    → onVertices (intervalMap M) (onVertices S x) ≡ x)
  (n : ℕ) → mapGrid M n ∘g gridSection S n ≡ idHom (Grid s n)
mapGrid-section M S split n = homExt (mapGrid-section-point M S split n)

-- Actual preimage data, with dimension-zero handled by its unique point.
-- This does not need truncation, enumeration of graph vertices or choice.
mapGrid-surjective : {r s : ℕ} (M : IntervalMorph r s)
  (S : Hom (Iₘ s) (Iₘ r))
  (split : (x : Fin (suc s))
    → onVertices (intervalMap M) (onVertices S x) ≡ x)
  (n : ℕ) (x : Vertex (Grid s n))
  → Σ[ y ∈ Vertex (Grid r n) ] (onVertices (mapGrid M n) y ≡ x)
mapGrid-surjective M S split n x =
  onVertices (gridSection S n) x , mapGrid-section-point M S split n x

changeSize-injective : {r s : ℕ} (M : IntervalMorph r s)
  (S : Hom (Iₘ s) (Iₘ r))
  (split : (x : Fin (suc s))
    → onVertices (intervalMap M) (onVertices S x) ≡ x)
  (G : Graph ℓ) (n : ℕ) (c d : Cell (Nₘ s G) n)
  → mapCells (changeSize M G) n c ≡ mapCells (changeSize M G) n d
  → c ≡ d
changeSize-injective M S split G n c d e = homExt λ x →
  sym (cong (onVertices c) (mapGrid-section-point M S split n x))
  ∙ cong (λ h → onVertices h (onVertices (gridSection S n) x)) e
  ∙ cong (onVertices d) (mapGrid-section-point M S split n x)

leftTransition-injective : (m : ℕ) (G : Graph ℓ) (n : ℕ)
  (c d : Cell (Nₘ m G) n)
  → mapCells (leftTransition m G) n c ≡ mapCells (leftTransition m G) n d
  → c ≡ d
leftTransition-injective m G =
  changeSize-injective (leftMorph m) (leftSection m) (left-section m) G

rightTransition-injective : (m : ℕ) (G : Graph ℓ) (n : ℕ)
  (c d : Cell (Nₘ m G) n)
  → mapCells (rightTransition m G) n c ≡ mapCells (rightTransition m G) n d
  → c ≡ d
rightTransition-injective m G =
  changeSize-injective (rightMorph m) (rightSection m) (right-section m) G

chooseTransition-injective : (b : Bool) (m : ℕ) (G : Graph ℓ) (n : ℕ)
  (c d : Cell (Nₘ m G) n)
  → mapCells (chooseTransition b m G) n c
    ≡ mapCells (chooseTransition b m G) n d
  → c ≡ d
chooseTransition-injective true = leftTransition-injective
chooseTransition-injective false = rightTransition-injective

stageTransition-injective : (G : Graph ℓ) (k n : ℕ)
  (c d : Cell (Stage G k) n)
  → mapCells (stageTransition G k) n c ≡ mapCells (stageTransition G k) n d
  → c ≡ d
stageTransition-injective G k =
  chooseTransition-injective (evenStage k) (suc k) G

module _ (G : Graph ℓ) where
  private module T = Stages (Stage G) (stageTransition G)

  -- Any actual finite path in CK's alternating sequence is injective.
  -- The recursion uses the original stageTransition, not a replacement
  -- padding system or an assumed monomorphism interface.
  laterMap-injective : {k l : ℕ} (p : Later k l) (n : ℕ)
    (c d : Cell (Stage G k) n)
    → mapCells (T.laterMap p) n c ≡ mapCells (T.laterMap p) n d
    → c ≡ d
  laterMap-injective now n c d e = e
  laterMap-injective (next {l} p) n c d e = laterMap-injective p n c d
    (stageTransition-injective G l n _ _ e)

  advanceCell-injective : {k l : ℕ} (p : k ≤ l) (n : ℕ)
    (c d : Cell (Stage G k) n)
    → T.advanceCell p n c ≡ T.advanceCell p n d → c ≡ d
  advanceCell-injective p = laterMap-injective (fromLe p)
