{-# OPTIONS --cubical --safe #-}

-- A fully instantiated TEST geometry for the coend machinery.
-- Its disks consist only of finitely many discrete vertices.  It is
-- not the standard interval geometry and does not model DHH spaces.
module DHH.Realization.DiscreteCubes where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Data.Unit.Base using (tt)
open import DHH.Graph
open import DHH.Cubes
open import DHH.CubeCategory
open import DHH.Topology.Base
open import DHH.Realization.Coend
open import DHH.Topology.WeakEquivalence

DiscreteCubeDiagram : DiskDiagram CubeCategory ℓ-zero
disk DiscreteCubeDiagram n = discreteTop (Vertex (Q n) , vertex-isSet (Q n))
diskMap DiscreteCubeDiagram {a} {b} u =
  fromDiscrete (Vertex (Q a) , vertex-isSet (Q a))
    (disk DiscreteCubeDiagram b) (onVertices (underlying u))
disk-id DiscreteCubeDiagram = continuousExt λ _ → refl
disk-compose DiscreteCubeDiagram f g = continuousExt λ _ → refl

DiscreteCubeGeometry : CubeGeometry ℓ-zero
diagram DiscreteCubeGeometry = DiscreteCubeDiagram
zeroPoint DiscreteCubeGeometry = tt
zero-contractible DiscreteCubeGeometry tt = refl
