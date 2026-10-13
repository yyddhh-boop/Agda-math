{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.Nerve where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.GraphSets
open import DHH.Cubes using (Q)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.StableNerve.Grid

private variable ℓ ℓ' : Level

module _ (r : ℕ) {m n : ℕ} (u : CubicalMap m n) where
  LiftsThresholds : Hom (Grid r m) (Grid r n) → Type₀
  LiftsThresholds h = (t : Fin r) (x : Vertex (Grid r m))
    → thresholdGrid t n (onVertices h x) ≡ onVertices (underlying u) (thresholdGrid t m x)

  lifts-prop : (h : Hom (Grid r m) (Grid r n)) → isProp (LiftsThresholds h)
  lifts-prop h = isPropΠ2 (λ t x → vertex-isSet (Q n) _ _)

  lifts-unique : (h k : Hom (Grid r m) (Grid r n)) → LiftsThresholds h → LiftsThresholds k → h ≡ k
  lifts-unique h k ph pk = homExt λ x → thresholdGrid-ext n _ _ λ t → ph t x ∙ sym (pk t x)

  LiftCandidate : Type₀
  LiftCandidate = Σ (Hom (Grid r m) (Grid r n)) LiftsThresholds

  candidate-prop : isProp LiftCandidate
  candidate-prop (h , ph) (k , pk) = Σ≡Prop lifts-prop (lifts-unique h k ph pk)

  candidate : LiftCandidate
  candidate = PT.rec candidate-prop
    (λ { (w , p) → evaluateGrid r w , λ t x → threshold-word r w t x
      ∙ cong (λ f → onVertices f (thresholdGrid t m x)) p }) (generated u)

  gridAction : Hom (Grid r m) (Grid r n)
  gridAction = fst candidate

  gridAction-threshold : LiftsThresholds gridAction
  gridAction-threshold = snd candidate

gridAction-word : (r : ℕ) {m n : ℕ} (w : CubeWord m n)
  → gridAction r (wordMap w) ≡ evaluateGrid r w
gridAction-word r w = refl

gridAction-id : (r n : ℕ) → gridAction r (cubeId n) ≡ idHom (Grid r n)
gridAction-id r n = refl

gridAction-compose : (r : ℕ) {m n k : ℕ} (f : CubicalMap m n) (g : CubicalMap n k)
  → gridAction r (f ⋆c g) ≡ gridAction r g ∘g gridAction r f
gridAction-compose r {m} {n} {k} f g = homExt λ x → thresholdGrid-ext k _ _ λ t →
  gridAction-threshold r (f ⋆c g) t x
  ∙ sym (gridAction-threshold r g t (onVertices (gridAction r f) x)
    ∙ cong (onVertices (underlying g)) (gridAction-threshold r f t x))

-- Every cube size is an ACTUAL presheaf on the same semantic cube
-- category as N₁.  Threshold separation proves independence of the
-- chosen word witness, including all connection/face/degeneracy laws.
Nₘ : (r : ℕ) → Graph ℓ → CubicalSet ℓ
cells (Nₘ r G) n = Hom (Grid r n) G , isSetGraphHom
reindex (Nₘ r G) u c = c ∘g gridAction r u
reindex-id (Nₘ r G) c = rightIdentity c
reindex-compose (Nₘ r G) f g c = cong (c ∘g_) (gridAction-compose r f g)
  ∙ homExt (λ _ → refl)

Nₘ-map : (r : ℕ) {G : Graph ℓ} {H : Graph ℓ'} → Hom G H → CubicalNatural (Nₘ r G) (Nₘ r H)
mapCells (Nₘ-map r f) n c = f ∘g c
natural (Nₘ-map r f) u c = homExt (λ _ → refl)

Nₘ-map-id : (r : ℕ) (G : Graph ℓ) → Nₘ-map r (idHom G) ≡ cubicalId (Nₘ r G)
Nₘ-map-id r G = cubicalNaturalExt (λ n c → leftIdentity c)

Nₘ-map-compose : (r : ℕ) {G H K : Graph ℓ} (f : Hom G H) (g : Hom H K)
  → Nₘ-map r (g ∘g f) ≡ Nₘ-map r f ⋆n Nₘ-map r g
Nₘ-map-compose r f g = cubicalNaturalExt (λ n c → associativity g f c)
