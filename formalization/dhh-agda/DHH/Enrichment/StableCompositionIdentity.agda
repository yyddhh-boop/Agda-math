{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.StableCompositionIdentity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; max)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans; left-≤-max; right-≤-max)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.Cubical.DayAssociatorHelpers using (dayTensorExt)
open import DHH.Cubical.DayTriple
open import DHH.Cubical.DayAssociator
open import DHH.Cubical.DayUnitLift
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Colimit
open import DHH.StableNerve.CommonStage
open import DHH.Enrichment.GraphHom
open import DHH.Enrichment.StableComposition
open import DHH.Enrichment.GridCompositionCoherence

private variable ℓ : Level

-- The unit is an actual natural transformation from the lifted Day
-- tensor unit. Every cell is the constant grid of graph identities.
stableIdentity : (G : Graph ℓ)
  → CubicalNatural (DayUnitAt ℓ) (N∞ (HomGraph G G))
mapCells (stableIdentity G) n v = Stable.point (HomGraph G G) n
  (zero , constantHom (HomGraph G G) (idHom G))
natural (stableIdentity G) {m} f v =
  cong (λ c → Stable.point (HomGraph G G) m (zero , c)) (homExt (λ _ → refl))

-- The alternating selector is deliberately eliminated: an opaque
-- evenStage k cannot definitionally reduce a constant transition.
abstract
  chooseTransition-constant : (which : Bool) (r n : ℕ) (T : Graph ℓ) (x : Vertex T)
    → mapCells (chooseTransition which r T) n (constantHom T x)
      ≡ constantHom T x
  chooseTransition-constant true r n T x = homExt (λ _ → refl)
  chooseTransition-constant false r n T x = homExt (λ _ → refl)

-- A constant grid remains constant under each stage transition.
-- This explicit induction makes the stable unit available at any
-- common stage; no choice of a stable representative is involved.
abstract
  stableIdentity-at-stage : (G : Graph ℓ) (k n : ℕ) (v : Cell (DayUnitAt ℓ) n)
    → mapCells (stableIdentity G) n v
      ≡ mapCells (includeStage (HomGraph G G) k) n
        (constantHom (HomGraph G G) (idHom G))
  stableIdentity-at-stage G zero n v = refl
  stableIdentity-at-stage G (suc k) n v =
    stableIdentity-at-stage G k n v
    ∙ SQ.eq/ _ _ (Stable.step {G = HomGraph G G} {n = n} {k = k}
      (constantHom (HomGraph G G) (idHom G)))
    ∙ cong (λ c → Stable.point (HomGraph G G) n (suc k , c))
      (chooseTransition-constant (evenStage k) (suc k) n (HomGraph G G) (idHom G))

