{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.Grid where

open import Cubical.Foundations.Prelude hiding (Cube; lower)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt; isPropUnit)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.GraphSets
open import DHH.Cubes using (PointGraph; Q; Position; here; there; boxHom; meetBool; joinBool)
import DHH.Cubes as UnitCube
open import DHH.CubeCategory
open import DHH.StableNerve.Interval

Grid : ℕ → ℕ → Graph ℓ-zero
Grid m zero = PointGraph
Grid m (suc n) = Iₘ m BOX Grid m n

insertGrid : (m : ℕ) {n : ℕ} → Position (suc n) → Bool → Vertex (Grid m n) → Vertex (Grid m (suc n))
insertGrid m here b x = endpoint m b , x
insertGrid m {suc n} (there i) b (a , x) = a , insertGrid m i b x

deleteGrid : (m : ℕ) {n : ℕ} → Position (suc n) → Vertex (Grid m (suc n)) → Vertex (Grid m n)
deleteGrid m here (a , x) = x
deleteGrid m {suc n} (there i) (a , x) = a , deleteGrid m i x

gridFace : (m : ℕ) {n : ℕ} → Position (suc n) → Bool → Hom (Grid m n) (Grid m (suc n))
onVertices (gridFace m i b) = insertGrid m i b
preserves (gridFace m here b) e = ∣ inl (refl , e) ∣₁
preserves (gridFace m {suc n} (there i) b) e = preserves (boxHom (idHom (Iₘ m)) (gridFace m i b)) e

gridDelete : (m : ℕ) {n : ℕ} → Position (suc n) → Hom (Grid m (suc n)) (Grid m n)
onVertices (gridDelete m i) = deleteGrid m i
preserves (gridDelete m {n} here) {x = (a , u)} {y = (b , v)} = PT.rec (adj-isProp (Grid m n) u v) λ where
  (inl (p , e)) → e
  (inr (e , p)) → subst (Adj (Grid m n) u) p (adj-refl (Grid m n) u)
preserves (gridDelete m {suc n} (there i)) e = preserves (boxHom (idHom (Iₘ m)) (gridDelete m i)) e

mergeGrid : (m : ℕ) {n : ℕ} → Position (suc n)
  → (Fin (suc m) → Fin (suc m) → Fin (suc m))
  → Vertex (Grid m (suc (suc n))) → Vertex (Grid m (suc n))
mergeGrid m here op (a , b , x) = op a b , x
mergeGrid m {suc n} (there i) op (a , x) = a , mergeGrid m i op x

gridConnection : (m : ℕ) {n : ℕ} (i : Position (suc n))
  (op : Fin (suc m) → Fin (suc m) → Fin (suc m))
  (left : {a a' : Fin (suc m)} → Near a a' → (b : Fin (suc m)) → Near (op a b) (op a' b))
  (right : (a : Fin (suc m)) {b b' : Fin (suc m)} → Near b b' → Near (op a b) (op a b'))
  → Hom (Grid m (suc (suc n))) (Grid m (suc n))
onVertices (gridConnection m i op left right) = mergeGrid m i op
preserves (gridConnection m {n} here op left right)
  {x = (a , b , u)} {y = (a' , b' , v)} = PT.rec (adj-isProp (Grid m (suc n)) _ _) λ where
  (inl (p , e)) → PT.rec (adj-isProp (Grid m (suc n)) _ _)
    (λ where
      (inl (q , e')) → ∣ inl (cong₂ op p q , e') ∣₁
      (inr (e' , q)) → ∣ inr (subst (λ z → Near (op a b) (op z b')) p (right a {b} {b'} e') , q) ∣₁) e
  (inr (e , p)) → ∣ inr (subst (λ z → Near (op a b) (op a' z)) (cong fst p) (left {a} {a'} e b) , cong snd p) ∣₁
preserves (gridConnection m {suc n} (there i) op left right) e =
  preserves (boxHom (idHom (Iₘ m)) (gridConnection m i op left right)) e

gridMin gridMax : (m : ℕ) {n : ℕ} → Position (suc n) → Hom (Grid m (suc (suc n))) (Grid m (suc n))
gridMin m i = gridConnection m i minFin (λ {a} {b} e z → min-near-left {m} {a} {b} e z) (λ z {a} {b} e → min-near-right {m} z {a} {b} e)
gridMax m i = gridConnection m i maxFin (λ {a} {b} e z → max-near-left {m} {a} {b} e z) (λ z {a} {b} e → max-near-right {m} z {a} {b} e)

evaluateGrid : (r : ℕ) {m n : ℕ} → CubeWord m n → Hom (Grid r m) (Grid r n)
evaluateGrid r identityW = idHom _
evaluateGrid r (faceW i b) = gridFace r i b
evaluateGrid r (deleteW i) = gridDelete r i
evaluateGrid r (minW i) = gridMin r i
evaluateGrid r (maxW i) = gridMax r i
evaluateGrid r (composeW u v) = evaluateGrid r v ∘g evaluateGrid r u

thresholdGrid : {r : ℕ} (t : Fin r) (n : ℕ) → Vertex (Grid r n) → Vertex (Q n)
thresholdGrid t zero x = x
thresholdGrid t (suc n) (a , x) = threshold t a , thresholdGrid t n x

thresholdGrid-ext : {r : ℕ} (n : ℕ) (x y : Vertex (Grid r n))
  → ((t : Fin r) → thresholdGrid t n x ≡ thresholdGrid t n y) → x ≡ y
thresholdGrid-ext zero x y p = isPropUnit x y
thresholdGrid-ext (suc n) (a , x) (b , y) p = cong₂ _,_
  (threshold-ext a b (λ t → cong fst (p t)))
  (thresholdGrid-ext n x y (λ t → cong snd (p t)))

threshold-insert : {r n : ℕ} (t : Fin r) (i : Position (suc n)) (b : Bool) (x : Vertex (Grid r n))
  → thresholdGrid t (suc n) (insertGrid r i b x)
    ≡ UnitCube.insert i b (thresholdGrid t n x)
threshold-insert {n = n} t here b x = cong (λ a → a , thresholdGrid t n x) (threshold-endpoint t b)
threshold-insert {n = suc n} t (there i) b (a , x) = cong (λ y → threshold t a , y) (threshold-insert t i b x)

threshold-delete : {r n : ℕ} (t : Fin r) (i : Position (suc n)) (x : Vertex (Grid r (suc n)))
  → thresholdGrid t n (deleteGrid r i x) ≡ UnitCube.delete i (thresholdGrid t (suc n) x)
threshold-delete t here (a , x) = refl
threshold-delete {n = suc n} t (there i) (a , x) = cong (λ y → threshold t a , y) (threshold-delete t i x)

threshold-merge : {r n : ℕ} (t : Fin r) (i : Position (suc n))
  (op : Fin (suc r) → Fin (suc r) → Fin (suc r)) (boolOp : Bool → Bool → Bool)
  (compatible : (a b : Fin (suc r)) → threshold t (op a b) ≡ boolOp (threshold t a) (threshold t b))
  (x : Vertex (Grid r (suc (suc n))))
  → thresholdGrid t (suc n) (mergeGrid r i op x)
    ≡ UnitCube.merge i boolOp (thresholdGrid t (suc (suc n)) x)
threshold-merge {n = n} t here op boolOp compatible (a , b , x) = cong (λ y → y , thresholdGrid t n x) (compatible a b)
threshold-merge {n = suc n} t (there i) op boolOp compatible (a , x) =
  cong (λ y → threshold t a , y) (threshold-merge t i op boolOp compatible x)

threshold-word : (r : ℕ) {m n : ℕ} (w : CubeWord m n) (t : Fin r) (x : Vertex (Grid r m))
  → thresholdGrid t n (onVertices (evaluateGrid r w) x)
    ≡ onVertices (evaluate w) (thresholdGrid t m x)
threshold-word r identityW t x = refl
threshold-word r (faceW i b) t x = threshold-insert t i b x
threshold-word r (deleteW i) t x = threshold-delete t i x
threshold-word r (minW i) t x = threshold-merge t i minFin meetBool (threshold-min t) x
threshold-word r (maxW i) t x = threshold-merge t i maxFin joinBool (threshold-max t) x
threshold-word r (composeW u v) t x = threshold-word r v t (onVertices (evaluateGrid r u) x)
  ∙ cong (onVertices (evaluate v)) (threshold-word r u t x)

-- Semantic Boolean equality descends to every finite ordered interval.
-- Positive thresholds separate finite-chain vertices and preserve min/max.
word-grid-ext : (r : ℕ) {m n : ℕ} (u v : CubeWord m n)
  → evaluate u ≡ evaluate v → evaluateGrid r u ≡ evaluateGrid r v
word-grid-ext r {m = m} {n = n} u v p = homExt λ x → thresholdGrid-ext n _ _ λ t →
  threshold-word r u t x
  ∙ cong (λ f → onVertices f (thresholdGrid t m x)) p
  ∙ sym (threshold-word r v t x)
