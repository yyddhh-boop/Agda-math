{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.Transitions where
open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Bool using (Bool; false; true; not)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.GraphSets
open import DHH.Cubes using (Position; here; there; boxHom)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.StableNerve.Interval
open import DHH.StableNerve.IntervalLaws
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve

private variable ℓ ℓ' : Level

-- A reusable lemma package; the l/r maps below supply every field by
-- explicit proofs.  This is not an assumed transition-system interface.
record IntervalMorph (r s : ℕ) : Type₀ where
  field
    intervalMap : Hom (Iₘ r) (Iₘ s)
    endpoints : (b : Bool) → onVertices intervalMap (endpoint r b) ≡ endpoint s b
    minimum : (a b : Fin (suc r)) → onVertices intervalMap (minFin a b)
      ≡ minFin (onVertices intervalMap a) (onVertices intervalMap b)
    maximum : (a b : Fin (suc r)) → onVertices intervalMap (maxFin a b)
      ≡ maxFin (onVertices intervalMap a) (onVertices intervalMap b)
open IntervalMorph public

leftMorph : (m : ℕ) → IntervalMorph (suc m) m
intervalMap (leftMorph m) = leftMap m
endpoints (leftMorph m) = left-endpoint m
minimum (leftMorph m) = left-min
maximum (leftMorph m) = left-max
rightMorph : (m : ℕ) → IntervalMorph (suc m) m
intervalMap (rightMorph m) = rightMap m
endpoints (rightMorph m) = right-endpoint m
minimum (rightMorph m) = right-min
maximum (rightMorph m) = right-max

mapGrid : {r s : ℕ} → IntervalMorph r s → (n : ℕ) → Hom (Grid r n) (Grid s n)
mapGrid M zero = idHom _
mapGrid M (suc n) = boxHom (intervalMap M) (mapGrid M n)

module _ {r s : ℕ} (M : IntervalMorph r s) where
  map-insert : {n : ℕ} (i : Position (suc n)) (b : Bool) (x : Vertex (Grid r n))
    → onVertices (mapGrid M (suc n)) (insertGrid r i b x)
      ≡ insertGrid s i b (onVertices (mapGrid M n) x)
  map-insert {n} here b x = cong (λ a → a , onVertices (mapGrid M n) x) (endpoints M b)
  map-insert {suc n} (there i) b (a , x) = cong (λ y → onVertices (intervalMap M) a , y) (map-insert i b x)

  map-delete : {n : ℕ} (i : Position (suc n)) (x : Vertex (Grid r (suc n)))
    → onVertices (mapGrid M n) (deleteGrid r i x)
      ≡ deleteGrid s i (onVertices (mapGrid M (suc n)) x)
  map-delete here (a , x) = refl
  map-delete {suc n} (there i) (a , x) = cong (λ y → onVertices (intervalMap M) a , y) (map-delete i x)

  map-merge : {n : ℕ} (i : Position (suc n))
    (opR : Fin (suc r) → Fin (suc r) → Fin (suc r))
    (opS : Fin (suc s) → Fin (suc s) → Fin (suc s))
    (compatible : (a b : Fin (suc r)) → onVertices (intervalMap M) (opR a b)
      ≡ opS (onVertices (intervalMap M) a) (onVertices (intervalMap M) b))
    (x : Vertex (Grid r (suc (suc n))))
    → onVertices (mapGrid M (suc n)) (mergeGrid r i opR x)
      ≡ mergeGrid s i opS (onVertices (mapGrid M (suc (suc n))) x)
  map-merge {n} here opR opS compatible (a , b , x) = cong (λ y → y , onVertices (mapGrid M n) x) (compatible a b)
  map-merge {suc n} (there i) opR opS compatible (a , x) =
    cong (λ y → onVertices (intervalMap M) a , y) (map-merge i opR opS compatible x)

  map-word : {m n : ℕ} (w : CubeWord m n) (x : Vertex (Grid r m))
    → onVertices (mapGrid M n) (onVertices (evaluateGrid r w) x)
      ≡ onVertices (evaluateGrid s w) (onVertices (mapGrid M m) x)
  map-word identityW x = refl
  map-word (faceW i b) x = map-insert i b x
  map-word (deleteW i) x = map-delete i x
  map-word (minW i) x = map-merge i minFin minFin (minimum M) x
  map-word (maxW i) x = map-merge i maxFin maxFin (maximum M) x
  map-word (composeW u v) x = map-word v (onVertices (evaluateGrid r u) x)
    ∙ cong (onVertices (evaluateGrid s v)) (map-word u x)

  gridAction-natural : {m n : ℕ} (u : CubicalMap m n)
    → mapGrid M n ∘g gridAction r u ≡ gridAction s u ∘g mapGrid M m
  gridAction-natural {m} {n} u = PT.rec (isSetGraphHom {G = Grid r m} {H = Grid s n} _ _)
    (λ { (w , p) → subst
      (λ (v : CubicalMap m n) → mapGrid M n ∘g gridAction r v ≡ gridAction s v ∘g mapGrid M m)
      (cubeMapExt {m = m} {n = n} {f = wordMap w} {g = u} p)
      (homExt {G = Grid r m} {H = Grid s n}
        {f = mapGrid M n ∘g evaluateGrid r w}
        {g = evaluateGrid s w ∘g mapGrid M m} (map-word w)) }) (generated u)

changeSize : {r s : ℕ} (M : IntervalMorph r s) (G : Graph ℓ)
  → CubicalNatural (Nₘ s G) (Nₘ r G)
mapCells (changeSize M G) n c = c ∘g mapGrid M n
natural (changeSize M G) {m} {n} u c = homExt λ x →
  cong (onVertices c) (sym (cong (λ f → onVertices f x) (gridAction-natural M u)))

leftTransition rightTransition : (m : ℕ) (G : Graph ℓ) → CubicalNatural (Nₘ m G) (Nₘ (suc m) G)
leftTransition m G = changeSize (leftMorph m) G
rightTransition m G = changeSize (rightMorph m) G

evenStage : ℕ → Bool
evenStage zero = true
evenStage (suc n) = not (evenStage n)

chooseTransition : Bool → (m : ℕ) (G : Graph ℓ) → CubicalNatural (Nₘ m G) (Nₘ (suc m) G)
chooseTransition true m G = leftTransition m G
chooseTransition false m G = rightTransition m G

-- CK Proposition 3.5: N₁ --l*--> N₂ --r*--> N₃ --l*--> ...
Stage : (G : Graph ℓ) → ℕ → CubicalSet ℓ
Stage G k = Nₘ (suc k) G
stageTransition : (G : Graph ℓ) (k : ℕ) → CubicalNatural (Stage G k) (Stage G (suc k))
stageTransition G k = chooseTransition (evenStage k) (suc k) G

changeSize-graph-natural : {r s : ℕ} (M : IntervalMorph r s) {G : Graph ℓ} {H : Graph ℓ'} (f : Hom G H)
  → changeSize M G ⋆n Nₘ-map r f ≡ Nₘ-map s f ⋆n changeSize M H
changeSize-graph-natural M f = cubicalNaturalExt (λ n c → homExt (λ _ → refl))

chooseTransition-cells-natural : (b : Bool) (m : ℕ) {G : Graph ℓ} {H : Graph ℓ'}
  (f : Hom G H) (n : ℕ) (c : Cell (Nₘ m G) n)
  → mapCells (Nₘ-map (suc m) f) n (mapCells (chooseTransition b m G) n c)
    ≡ mapCells (chooseTransition b m H) n (mapCells (Nₘ-map m f) n c)
chooseTransition-cells-natural true m f n c = homExt (λ _ → refl)
chooseTransition-cells-natural false m f n c = homExt (λ _ → refl)

stageTransition-cells-natural : {G : Graph ℓ} {H : Graph ℓ'}
  (f : Hom G H) (k n : ℕ) (c : Cell (Stage G k) n)
  → mapCells (Nₘ-map (suc (suc k)) f) n (mapCells (stageTransition G k) n c)
    ≡ mapCells (stageTransition H k) n (mapCells (Nₘ-map (suc k) f) n c)
stageTransition-cells-natural f k = chooseTransition-cells-natural (evenStage k) (suc k) f
