{-# OPTIONS --cubical --safe #-}

module DHH.Cubical.FaceIntersections where

-- 交集的证明只使用语义顶点函数。若两个不同坐标的面表示同一个
-- cube map，删除一个剩余坐标即给出共同的余维二分解；删除是实际
-- 生成算子，故该分解仍在 CubeCategory 中，无需选取或规范化词。

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; false; true; false≢true)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥; elim)
open import DHH.Graph
open import DHH.Cubes using
  (Q; Position; here; there; insert; delete; delete-insert;
   CoordinatePair; front; under; lower; upper; lowerWide; upperWide;
   delete-insert-upper; delete-insert-lower; insert-distinct)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
import DHH.Cubical.FaceGluing as FG

private variable ℓ : Level

falseVertex : (n : ℕ) → Vertex (Q n)
falseVertex zero = tt
falseVertex (suc n) = false , falseVertex n

readCoordinate : {n : ℕ} → Position n → Vertex (Q n) → Bool
readCoordinate here = fst
readCoordinate (there i) (a , x) = readCoordinate i x

read-insert : {n : ℕ} (i : Position (suc n)) (b : Bool)
  (x : Vertex (Q n)) → readCoordinate i (insert i b x) ≡ b
read-insert here b x = refl
read-insert {n = suc n} (there i) b (a , x) = read-insert i b x

abstract
  face-mono : {m n : ℕ} (i : Position (suc n)) (b : Bool)
    (u v : CubicalMap m n)
    → u ⋆c cubeFace i b ≡ v ⋆c cubeFace i b → u ≡ v
  face-mono {m} {n} i b u v e = cubeMapExt {f = u} {g = v} (homExt λ x →
    sym (delete-insert i b (onVertices (underlying u) x))
    ∙ cong (delete i) (cong (λ f → onVertices (underlying f) x) e)
    ∙ delete-insert i b (onVertices (underlying v) x))

  face-endpoint-equal : {m n : ℕ} (i : Position (suc n)) (a b : Bool)
    (u v : CubicalMap m n)
    → u ⋆c cubeFace i a ≡ v ⋆c cubeFace i b → a ≡ b
  face-endpoint-equal {m} i a b u v e =
    sym (read-insert i a (onVertices (underlying u) (falseVertex m)))
    ∙ cong (λ f → readCoordinate i (onVertices (underlying f) (falseVertex m))) e
    ∙ read-insert i b (onVertices (underlying v) (falseVertex m))

  opposite-faces-disjoint : {m n : ℕ} (i : Position (suc n))
    (u v : CubicalMap m n)
    → u ⋆c cubeFace i false ≡ v ⋆c cubeFace i true → ⊥
  opposite-faces-disjoint i u v e = false≢true (face-endpoint-equal i false true u v e)

  cube-faces-commute : {n : ℕ} (p : CoordinatePair n) (a b : Bool)
    → cubeFace (upper p) b ⋆c cubeFace (lowerWide p) a
      ≡ cubeFace (lower p) a ⋆c cubeFace (upperWide p) b
  cube-faces-commute p a b = cubeMapExt (homExt (insert-distinct p a b))

-- 输出维数 n 的共同 map 由 u 后接 delete 得到。因此这不是一个
-- 只存在于任意图映射范畴、却无法保证 generated 的集合论分解。
DistinctFactorization : {m n : ℕ} (p : CoordinatePair n) (a b : Bool)
  (u v : CubicalMap m (suc n)) → Type₀
DistinctFactorization {m} {n} p a b u v = Σ[ w ∈ CubicalMap m n ]
  (u ≡ w ⋆c cubeFace (upper p) b) × (v ≡ w ⋆c cubeFace (lower p) a)

distinct-face-factorization : {m n : ℕ} (p : CoordinatePair n) (a b : Bool)
  (u v : CubicalMap m (suc n))
  → u ⋆c cubeFace (lowerWide p) a ≡ v ⋆c cubeFace (upperWide p) b
  → DistinctFactorization p a b u v
distinct-face-factorization {m} {n} p a b u v e = w , u-factor , v-factor
  where
  w : CubicalMap m n
  w = u ⋆c cubeDelete (upper p)

  v-factor : v ≡ w ⋆c cubeFace (lower p) a
  v-factor = cubeMapExt {f = v} {g = w ⋆c cubeFace (lower p) a} (homExt λ x →
    sym (delete-insert (upperWide p) b (onVertices (underlying v) x))
    ∙ sym (cong (delete (upperWide p)) (cong (λ f → onVertices (underlying f) x) e))
    ∙ delete-insert-lower p a (onVertices (underlying u) x))

  u-factor : u ≡ w ⋆c cubeFace (upper p) b
  u-factor = cubeMapExt {f = u} {g = w ⋆c cubeFace (upper p) b} (homExt λ x →
    sym (delete-insert (lowerWide p) a (onVertices (underlying u) x))
    ∙ cong (delete (lowerWide p)) (cong (λ f → onVertices (underlying f) x) e)
    ∙ cong (λ y → delete (lowerWide p) (insert (upperWide p) b y))
      (cong (λ f → onVertices (underlying f) x) v-factor)
    ∙ delete-insert-upper p b (insert (lower p) a (onVertices (underlying w) x))
    ∙ cong (insert (upper p) b) (delete-insert (lower p) a (onVertices (underlying w) x)))

-- 位置比较按共同前缀递归。首个不同坐标给出 front；共同前缀给出
-- under。由此每对不同位置都有一个有限 CoordinatePair 表示。
data PositionComparison : {d : ℕ} → Position d → Position d → Type₀ where
  same : {d : ℕ} (i : Position d) → PositionComparison i i
  forward : {n : ℕ} (p : CoordinatePair n)
    → PositionComparison (lowerWide p) (upperWide p)
  backward : {n : ℕ} (p : CoordinatePair n)
    → PositionComparison (upperWide p) (lowerWide p)

comparePositions : {d : ℕ} (i j : Position d) → PositionComparison i j
comparePositions here here = same here
comparePositions {d = suc (suc n)} here (there j) = forward (front j)
comparePositions {d = suc (suc n)} (there i) here = backward (front i)
comparePositions (there i) (there j) with comparePositions i j
... | same k = same (there k)
... | forward p = forward (under p)
... | backward p = backward (under p)

pairChoice : {d : ℕ} (i j : Position d) → PositionComparison i j
pairChoice = comparePositions

-- n=0 只有两个端点，因而余维二条件为空；其余维数只量化有限的
-- 坐标对及两个 Bool 端点，不再量化任意来源维数和任意重索引。
PairwiseAgreement : {n : ℕ} (S : FaceSelection n) (A : CubicalSet ℓ)
  → ((j : Facet n) → fst (S j) → Cell A n) → Type ℓ
PairwiseAgreement {ℓ = ℓ} {n = zero} S A cs = Lift {j = ℓ} Unit
PairwiseAgreement {n = suc n} S A cs =
  (r : CoordinatePair n) (a b : Bool)
  (p : fst (S (lowerWide r , a))) (q : fst (S (upperWide r , b)))
  → reindex A (cubeFace (upper r) b) (cs (lowerWide r , a) p)
    ≡ reindex A (cubeFace (lower r) a) (cs (upperWide r , b) q)

record PairwiseFaceData {n : ℕ} (S : FaceSelection n) (A : CubicalSet ℓ) : Type ℓ where
  field
    faceCells : (j : Facet n) → fst (S j) → Cell A n
    pairwiseAgreement : PairwiseAgreement S A faceCells
open PairwiseFaceData public

-- 共同余维二分解把任意高维来源的相交等式化为这一条生成等式的
-- 重索引。左右端先改写为 w 后接面，再应用预层复合律。
codim2-agreement : {n : ℕ} (S : FaceSelection (suc n)) (A : CubicalSet ℓ)
  (D : PairwiseFaceData S A) (r : CoordinatePair n) (a b : Bool)
  (p : fst (S (lowerWide r , a))) (q : fst (S (upperWide r , b)))
  {m : ℕ} (u v : CubicalMap m (suc n))
  → u ⋆c cubeFace (lowerWide r) a ≡ v ⋆c cubeFace (upperWide r) b
  → reindex A u (faceCells D (lowerWide r , a) p)
    ≡ reindex A v (faceCells D (upperWide r , b) q)
codim2-agreement S A D r a b p q u v e =
  cong (λ f → reindex A f (faceCells D (lowerWide r , a) p)) u-factor
  ∙ reindex-compose A w (cubeFace (upper r) b) (faceCells D (lowerWide r , a) p)
  ∙ cong (reindex A w) (pairwiseAgreement D r a b p q)
  ∙ sym (reindex-compose A w (cubeFace (lower r) a) (faceCells D (upperWide r , b) q))
  ∙ sym (cong (λ f → reindex A f (faceCells D (upperWide r , b) q)) v-factor)
  where
  result = distinct-face-factorization r a b u v e
  w = fst result
  u-factor = fst (snd result)
  v-factor = snd (snd result)

-- 同一面的重索引由单射性比较；选择证明不携带额外数据。
same-face-agreement : {m n : ℕ} (S : FaceSelection n) (A : CubicalSet ℓ)
  (D : PairwiseFaceData S A) (i : Position (suc n)) (b : Bool)
  (p q : fst (S (i , b))) (u v : CubicalMap m n)
  → u ⋆c cubeFace i b ≡ v ⋆c cubeFace i b
  → reindex A u (faceCells D (i , b) p) ≡ reindex A v (faceCells D (i , b) q)
same-face-agreement S A D i b p q u v e =
  cong (λ f → reindex A f (faceCells D (i , b) p)) (face-mono i b u v e)
  ∙ cong (reindex A v) (cong (faceCells D (i , b)) (snd (S (i , b)) p q))

same-position-agreement : {m n : ℕ} (S : FaceSelection n) (A : CubicalSet ℓ)
  (D : PairwiseFaceData S A) (i : Position (suc n)) (a b : Bool)
  (p : fst (S (i , a))) (q : fst (S (i , b))) (u v : CubicalMap m n)
  → u ⋆c cubeFace i a ≡ v ⋆c cubeFace i b
  → reindex A u (faceCells D (i , a) p) ≡ reindex A v (faceCells D (i , b) q)
same-position-agreement S A D i false false p q u v e = same-face-agreement S A D i false p q u v e
same-position-agreement S A D i true true p q u v e = same-face-agreement S A D i true p q u v e
same-position-agreement S A D i false true p q u v e = elim (opposite-faces-disjoint i u v e)
same-position-agreement S A D i true false p q u v e = elim (opposite-faces-disjoint i v u (sym e))

-- 维数也随比较证据消去，forward/backward 自动把 n 细化为 suc k。
-- 这样零维面的情形没有被误当成存在余维二立方体。
agreement-by-comparison : {m n : ℕ} (S : FaceSelection n) (A : CubicalSet ℓ)
  (D : PairwiseFaceData S A) (i j : Position (suc n))
  → PositionComparison i j → (a b : Bool)
  → (p : fst (S (i , a))) (q : fst (S (j , b))) (u v : CubicalMap m n)
  → u ⋆c cubeFace i a ≡ v ⋆c cubeFace j b
  → reindex A u (faceCells D (i , a) p) ≡ reindex A v (faceCells D (j , b) q)
agreement-by-comparison S A D i .i (same .i) a b p q u v e =
  same-position-agreement S A D i a b p q u v e
agreement-by-comparison S A D .(lowerWide r) .(upperWide r) (forward r) a b p q u v e =
  codim2-agreement S A D r a b p q u v e
agreement-by-comparison S A D .(upperWide r) .(lowerWide r) (backward r) a b p q u v e =
  sym (codim2-agreement S A D r b a q p v u (sym e))

module FiniteGluing {n : ℕ} (S : FaceSelection n) (A : CubicalSet ℓ)
  (D : PairwiseFaceData S A) where
  module G = FG.Gluing S A

  fromPairwise : G.FaceData
  G.faceCell fromPairwise = faceCells D
  G.agreeOnOverlap fromPairwise (i , a) (j , b) p q u v e =
    agreement-by-comparison S A D i j (pairChoice i j) a b p q u v e

  assemble : CubicalNatural (SelectedFaces.complex S) A
  assemble = G.assemble fromPairwise

  assemble-on-face : (j : Facet n) (p : fst (S j))
    → SelectedFaces.face S j p ⋆n assemble ≡ classifyCube A (faceCells D j p)
  assemble-on-face = G.assemble-on-face fromPairwise

  assemble-unique : (h : CubicalNatural (SelectedFaces.complex S) A)
    → ((j : Facet n) (p : fst (S j))
      → SelectedFaces.face S j p ⋆n h ≡ classifyCube A (faceCells D j p))
    → h ≡ assemble
  assemble-unique = G.assemble-unique fromPairwise

open FiniteGluing public using (fromPairwise)

-- 反向直接把全部 overlap 的条件限制到有限余维二面。与 fromPairwise
-- 合用可把现有 FaceGluing 的输入完整改写为上述有限判据。
toPairwise : {n : ℕ} (S : FaceSelection n) (A : CubicalSet ℓ)
  → FG.Gluing.FaceData S A → PairwiseFaceData S A
faceCells (toPairwise S A D) = FG.Gluing.faceCell {S = S} {A = A} D
pairwiseAgreement (toPairwise {n = zero} S A D) = lift tt
pairwiseAgreement (toPairwise {n = suc n} S A D) r a b p q =
  FG.Gluing.agreeOnOverlap {S = S} {A = A} D (lowerWide r , a) (upperWide r , b) p q
    (cubeFace (upper r) b) (cubeFace (lower r) a) (cube-faces-commute r a b)
