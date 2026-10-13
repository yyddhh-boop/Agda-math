{-# OPTIONS --cubical --safe #-}

module DHH.Geometry.RealCubeDiagram where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph using (_∘g_)
open import DHH.CubeCategory
open import DHH.Topology.Base
open import DHH.Topology.WeakEquivalence using (CubeGeometry; diagram; zeroPoint; zero-contractible)
open import DHH.Realization.Coend using (DiskDiagram; disk; diskMap; disk-id; disk-compose)
open import DHH.Geometry.RealCubes
open import DHH.Geometry.RealCubeDescent

-- Descend the continuous word interpretation along the ACTUAL
-- generated morphisms.  Weak constancy is the proved rational-gap
-- theorem, so no arbitrary choice of word or extra axiom is involved.
realCubeAction : {m n : ℕ} → CubicalMap m n → Continuous (RealCube m) (RealCube n)
realCubeAction {m} {n} u = PT.rec→Set (Continuous-isSet (RealCube m) (RealCube n))
  (λ { (w , p) → realCubeWord w })
  (λ { (w , p) (v , q) → realCubeWord-ext w v (p ∙ sym q) }) (generated u)

realCubeAction-word : {m n : ℕ} (w : CubeWord m n)
  → realCubeAction (wordMap w) ≡ realCubeWord w
realCubeAction-word w = refl

realCubeAction-choice : {m n : ℕ} (u : CubicalMap m n) (w : CubeWord m n)
  → evaluate w ≡ underlying u → realCubeAction u ≡ realCubeWord w
realCubeAction-choice u w eq =
  cong realCubeAction (cubeMapExt {f = u} {g = wordMap w} (sym eq))

realCubeAction-id : (n : ℕ) → realCubeAction (cubeId n) ≡ identityContinuous (RealCube n)
realCubeAction-id n = refl

realCubeAction-compose : {m n k : ℕ} (f : CubicalMap m n) (g : CubicalMap n k)
  → realCubeAction (f ⋆c g) ≡ composeContinuous (realCubeAction g) (realCubeAction f)
realCubeAction-compose {m} {n} {k} f g =
  PT.rec2 (Continuous-isSet (RealCube m) (RealCube k) _ _)
    (λ { (w , p) (v , q) →
      realCubeAction-choice (f ⋆c g) (composeW w v) (cong₂ _∘g_ q p)
      ∙ cong₂ composeContinuous
          (sym (realCubeAction-choice g v q)) (sym (realCubeAction-choice f w p)) })
    (generated f) (generated g)

standardCubeDiagram : DiskDiagram CubeCategory (ℓ-suc ℓ-zero)
disk standardCubeDiagram = RealCube
diskMap standardCubeDiagram = realCubeAction
disk-id standardCubeDiagram {a = n} = realCubeAction-id n
disk-compose standardCubeDiagram = realCubeAction-compose

standardCubeGeometry : CubeGeometry (ℓ-suc ℓ-zero)
diagram standardCubeGeometry = standardCubeDiagram
zeroPoint standardCubeGeometry = realCubeZero
zero-contractible standardCubeGeometry = realCubeZero-singleton
