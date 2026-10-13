{-# OPTIONS --cubical --safe #-}

module DHH.Topology.WeakEquivalence where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.Cubes using (Position; here; there)
open import DHH.CubeCategory
open import DHH.Topology.Base
open import DHH.Realization.Coend using (DiskDiagram; disk; diskMap)

-- A geometry is a concrete diagram of topological cubes, including its
-- zero-dimensional point.  The actual standard real-interval instance
-- is constructed in Geometry.RealCubeDiagram; it is not assumed here.
record CubeGeometry (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    diagram : DiskDiagram CubeCategory ℓ
    zeroPoint : Carrier (disk diagram zero)
    zero-contractible : (t : Carrier (disk diagram zero)) → t ≡ zeroPoint
open CubeGeometry public

module HomotopyGroups {ℓ : Level} (E : CubeGeometry ℓ) where
  D : DiskDiagram CubeCategory ℓ
  D = diagram E

  -- Topological paths are continuous maps of the one-dimensional disk.
  -- Equality in Carrier X is merely equality of points.
  record TopologicalPath (X : Top ℓ) (x y : Carrier X) : Type (ℓ-suc ℓ) where
    field
      pathMap : Continuous (disk D 1) X
      start : carrierMap pathMap
        (carrierMap (diskMap D (cubeFace here false)) (zeroPoint E)) ≡ x
      end : carrierMap pathMap
        (carrierMap (diskMap D (cubeFace here true)) (zeroPoint E)) ≡ y
  open TopologicalPath public

  Components : Top ℓ → Type (ℓ-suc ℓ)
  Components X = Carrier X SQ./ TopologicalPath X

  mapTopologicalPath : {X Y : Top ℓ} (f : Continuous X Y) {x y : Carrier X}
                    → TopologicalPath X x y
                    → TopologicalPath Y (carrierMap f x) (carrierMap f y)
  pathMap (mapTopologicalPath f p) = composeContinuous f (pathMap p)
  start (mapTopologicalPath f p) = cong (carrierMap f) (start p)
  end (mapTopologicalPath f p) = cong (carrierMap f) (end p)

  componentsMap : {X Y : Top ℓ} → Continuous X Y → Components X → Components Y
  componentsMap f = SQ.rec SQ.squash/ (λ x → SQ.[ carrierMap f x ])
    (λ x y p → SQ.eq/ _ _ (mapTopologicalPath f p))

  components-id : (X : Top ℓ) → componentsMap (identityContinuous X) ≡ (λ a → a)
  components-id X = funExt (SQ.elimProp (λ _ → SQ.squash/ _ _) (λ _ → refl))

  components-compose : {X Y Z : Top ℓ} (f : Continuous X Y) (g : Continuous Y Z)
                     → componentsMap (composeContinuous g f)
                       ≡ (λ a → componentsMap g (componentsMap f a))
  components-compose f g = funExt (SQ.elimProp (λ _ → SQ.squash/ _ _) (λ _ → refl))

  -- The index n denotes dimension n+1, hence these are all POSITIVE
  -- homotopy groups.  The entire cubical boundary is fixed at x.
  record BasedCube (X : Top ℓ) (x : Carrier X) (n : ℕ) : Type (ℓ-suc ℓ) where
    field
      cubeMap : Continuous (disk D (suc n)) X
      boundary : (i : Position (suc n)) (b : Bool) (t : Carrier (disk D n))
               → carrierMap cubeMap (carrierMap (diskMap D (cubeFace i b)) t) ≡ x
  open BasedCube public

  basedCubeExt : {X : Top ℓ} {x : Carrier X} {n : ℕ} {a b : BasedCube X x n}
               → cubeMap a ≡ cubeMap b → a ≡ b
  cubeMap (basedCubeExt p i) = p i
  boundary (basedCubeExt {X} {x} {n} {a} {b} p i) j e t =
    isProp→PathP
      (λ i → carrier-isSet X
        (carrierMap (p i) (carrierMap (diskMap D (cubeFace j e)) t)) x)
      (boundary a j e t) (boundary b j e t) i

  record BasedHomotopy {X : Top ℓ} {x : Carrier X} {n : ℕ}
                       (f g : BasedCube X x n) : Type (ℓ-suc ℓ) where
    field
      homotopyMap : Continuous (disk D (suc (suc n))) X
      endpoint0 : (t : Carrier (disk D (suc n)))
                → carrierMap homotopyMap
                    (carrierMap (diskMap D (cubeFace here false)) t)
                  ≡ carrierMap (cubeMap f) t
      endpoint1 : (t : Carrier (disk D (suc n)))
                → carrierMap homotopyMap
                    (carrierMap (diskMap D (cubeFace here true)) t)
                  ≡ carrierMap (cubeMap g) t
      fixedBoundary : (i : Position (suc n)) (b : Bool)
                      (t : Carrier (disk D (suc n)))
                    → carrierMap homotopyMap
                        (carrierMap (diskMap D (cubeFace (there i) b)) t) ≡ x
  open BasedHomotopy public

  -- Only the set of homotopy classes is needed to define a weak
  -- equivalence.  Group operations are not silently postulated here.
  Pi : (X : Top ℓ) → Carrier X → ℕ → Type (ℓ-suc ℓ)
  Pi X x n = BasedCube X x n SQ./ BasedHomotopy

  mapBasedCube : {X Y : Top ℓ} (f : Continuous X Y) {x : Carrier X} {n : ℕ}
               → BasedCube X x n → BasedCube Y (carrierMap f x) n
  cubeMap (mapBasedCube f a) = composeContinuous f (cubeMap a)
  boundary (mapBasedCube f a) i b t = cong (carrierMap f) (boundary a i b t)

  mapBasedHomotopy : {X Y : Top ℓ} (f : Continuous X Y)
                    {x : Carrier X} {n : ℕ} {a b : BasedCube X x n}
                  → BasedHomotopy a b
                  → BasedHomotopy (mapBasedCube f a) (mapBasedCube f b)
  homotopyMap (mapBasedHomotopy f h) = composeContinuous f (homotopyMap h)
  endpoint0 (mapBasedHomotopy f h) t = cong (carrierMap f) (endpoint0 h t)
  endpoint1 (mapBasedHomotopy f h) t = cong (carrierMap f) (endpoint1 h t)
  fixedBoundary (mapBasedHomotopy f h) i b t =
    cong (carrierMap f) (fixedBoundary h i b t)

  piMap : {X Y : Top ℓ} (f : Continuous X Y) (x : Carrier X) (n : ℕ)
        → Pi X x n → Pi Y (carrierMap f x) n
  piMap f x n = SQ.rec SQ.squash/ (λ a → SQ.[ mapBasedCube f a ])
    (λ a b h → SQ.eq/ _ _ (mapBasedHomotopy f h))

  pi-id : (X : Top ℓ) (x : Carrier X) (n : ℕ)
        → piMap (identityContinuous X) x n ≡ (λ a → a)
  pi-id X x n = funExt (SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ a → cong SQ.[_] (basedCubeExt (continuous-left-id (cubeMap a)))))

  pi-compose : {X Y Z : Top ℓ} (f : Continuous X Y) (g : Continuous Y Z)
               (x : Carrier X) (n : ℕ)
             → piMap (composeContinuous g f) x n
               ≡ (λ a → piMap g (carrierMap f x) n (piMap f x n a))
  pi-compose f g x n = funExt (SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ a → cong SQ.[_] (basedCubeExt (sym (continuous-assoc (cubeMap a) f g)))))

  record WeakHomotopyEquivalence {X Y : Top ℓ} (f : Continuous X Y)
                                : Type (ℓ-suc ℓ) where
    field
      components-equiv : isEquiv (componentsMap f)
      all-pi-equiv : (x : Carrier X) (n : ℕ) → isEquiv (piMap f x n)
  open WeakHomotopyEquivalence public

  weak-isProp : {X Y : Top ℓ} (f : Continuous X Y)
              → isProp (WeakHomotopyEquivalence f)
  components-equiv (weak-isProp f p q i) =
    isPropIsEquiv (componentsMap f) (components-equiv p) (components-equiv q) i
  all-pi-equiv (weak-isProp f p q i) x n =
    isPropIsEquiv (piMap f x n) (all-pi-equiv p x n) (all-pi-equiv q x n) i

  weak-id : (X : Top ℓ) → WeakHomotopyEquivalence (identityContinuous X)
  components-equiv (weak-id X) = subst isEquiv (sym (components-id X)) (snd (idEquiv _))
  all-pi-equiv (weak-id X) x n = subst isEquiv (sym (pi-id X x n)) (snd (idEquiv _))

  weak-compose : {X Y Z : Top ℓ} (f : Continuous X Y) (g : Continuous Y Z)
               → WeakHomotopyEquivalence f → WeakHomotopyEquivalence g
               → WeakHomotopyEquivalence (composeContinuous g f)
  components-equiv (weak-compose f g p q) =
    subst isEquiv (sym (components-compose f g))
      (snd (compEquiv (_ , components-equiv p) (_ , components-equiv q)))
  all-pi-equiv (weak-compose f g p q) x n =
    subst isEquiv (sym (pi-compose f g x n))
      (snd (compEquiv (_ , all-pi-equiv p x n)
        (_ , all-pi-equiv q (carrierMap f x) n)))
