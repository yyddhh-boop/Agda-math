{-# OPTIONS --cubical --safe #-}

module DHH.StableNerve.HornFaceEvaluation where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Bool using (Bool; false; true; false≢true)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using () renaming (rec to emptyRec)
open import DHH.Graph
open import DHH.Cubes using (Position; CoordinatePair; lower; upper; lowerWide; upperWide)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.Cubical.FaceIntersections using
  (cube-faces-commute; PositionComparison; same; forward; backward; comparePositions)
open import DHH.StableNerve.Grid
open import DHH.StableNerve.GridFaces
open import DHH.StableNerve.Nerve

private variable ℓ : Level

-- 对任意选择 S 而非仅一个 horn：η 限制到选面给出实际网格图同态。
-- E 的 preserves 字段就是该生成面中的边被送往 H 的边的证明。
-- 只在后面的“同一环境点”定理要求 m 正；重索引相容对 m = 0 也成立。
module _ (m : ℕ) {H : Graph ℓ} where
  E : {n : ℕ} (S : FaceSelection n)
    → CubicalNatural (SelectedFaces.complex S) (Nₘ m H)
    → (j : Facet n) → fst (S j) → Hom (Grid m n) H
  E {n} S η j p = mapCells η n
    (mapCells (SelectedFaces.face S j p) n (cubeId n))

  -- Yoneda 的已验证自然性把“先限制面再评价”与“先评价再限制”连接。
  E-reindex : {n : ℕ} (S : FaceSelection n)
    (η : CubicalNatural (SelectedFaces.complex S) (Nₘ m H))
    (j : Facet n) (p : fst (S j)) {d : ℕ} (u : CubicalMap d n)
    → E S η j p ∘g gridAction m u
      ≡ mapCells η d (mapCells (SelectedFaces.face S j p) d u)
  E-reindex S η j p {d} u = cong (λ h → mapCells h d u)
    (every-natural-classified (Nₘ m H) (SelectedFaces.face S j p ⋆n η))

  E-overlap : {n : ℕ} (S : FaceSelection n)
    (η : CubicalNatural (SelectedFaces.complex S) (Nₘ m H))
    (j k : Facet n) (p : fst (S j)) (q : fst (S k))
    {d : ℕ} (u v : CubicalMap d n)
    → u ⋆c facetMap j ≡ v ⋆c facetMap k
    → E S η j p ∘g gridAction m u ≡ E S η k q ∘g gridAction m v
  E-overlap S η j k p q {d} u v e = E-reindex S η j p u
    ∙ cong (mapCells η d)
      (SelectedFaces.inclusion-injective S
        (mapCells (SelectedFaces.face S j p) d u)
        (mapCells (SelectedFaces.face S k q) d v) e)
    ∙ sym (E-reindex S η k q v)

  -- 两个选面在共同余维二面上的实际图同态相同。
  -- 这里比较的是预层重索引，不假定图余端 Γ 保持单射。
  E-codim2 : {n : ℕ} (S : FaceSelection (suc n))
    (η : CubicalNatural (SelectedFaces.complex S) (Nₘ m H))
    (c : CoordinatePair n) (a b : Bool)
    (p : fst (S (lowerWide c , a))) (q : fst (S (upperWide c , b)))
    → E S η (lowerWide c , a) p ∘g gridFace m (upper c) b
      ≡ E S η (upperWide c , b) q ∘g gridFace m (lower c) a
  E-codim2 S η c a b p q = E-overlap S η
    (lowerWide c , a) (upperWide c , b) p q
    (cubeFace (upper c) b) (cubeFace (lower c) a) (cube-faces-commute c a b)

  E-same-face : {n : ℕ} (S : FaceSelection n)
    (η : CubicalNatural (SelectedFaces.complex S) (Nₘ m H))
    (i : Position (suc n)) (b : Bool) (p q : fst (S (i , b)))
    (x y : Vertex (Grid m n))
    → insertGrid m i b x ≡ insertGrid m i b y
    → onVertices (E S η (i , b) p) x ≡ onVertices (E S η (i , b) q) y
  E-same-face S η i b p q x y e =
    cong (onVertices (E S η (i , b) p)) (grid-face-mono m i b x y e)
    ∙ cong (λ t → onVertices (E S η (i , b) t) y) (snd (S (i , b)) p q)

  -- 删除另一个坐标构造共同点，再用 E-codim2 比较其两个面表示。
  E-distinct-face : {n : ℕ} (S : FaceSelection (suc n))
    (η : CubicalNatural (SelectedFaces.complex S) (Nₘ m H))
    (c : CoordinatePair n) (a b : Bool)
    (p : fst (S (lowerWide c , a))) (q : fst (S (upperWide c , b)))
    (x y : Vertex (Grid m (suc n)))
    → insertGrid m (lowerWide c) a x ≡ insertGrid m (upperWide c) b y
    → onVertices (E S η (lowerWide c , a) p) x
      ≡ onVertices (E S η (upperWide c , b) q) y
  E-distinct-face S η c a b p q x y e =
    cong (onVertices (E S η (lowerWide c , a) p)) (fst (snd f))
    ∙ cong (λ h → onVertices h (fst f)) (E-codim2 S η c a b p q)
    ∙ sym (cong (onVertices (E S η (upperWide c , b) q)) (snd (snd f)))
    where
    f = grid-distinct-face-factorization m c a b x y e

module _ (r : ℕ) {H : Graph ℓ} where
  -- 相同坐标的相反端点由正长度区间的第一个阈值排除。
  E-same-position : {n : ℕ} (S : FaceSelection n)
    (η : CubicalNatural (SelectedFaces.complex S) (Nₘ (suc r) H))
    (i : Position (suc n)) (a b : Bool)
    (p : fst (S (i , a))) (q : fst (S (i , b)))
    (x y : Vertex (Grid (suc r) n))
    → insertGrid (suc r) i a x ≡ insertGrid (suc r) i b y
    → onVertices (E (suc r) S η (i , a) p) x
      ≡ onVertices (E (suc r) S η (i , b) q) y
  E-same-position S η i false false p q x y e = E-same-face (suc r) S η i false p q x y e
  E-same-position S η i true true p q x y e = E-same-face (suc r) S η i true p q x y e
  E-same-position S η i false true p q x y e =
    emptyRec (false≢true (grid-face-endpoint-equal r i false true x y e))
  E-same-position S η i true false p q x y e =
    emptyRec (false≢true (grid-face-endpoint-equal r i false true y x (sym e)))

  -- comparePositions 递归比较坐标；forward/backward 同时细化维数。
  -- 因此零维面只走 same 分支，无须假造余维二对象。
  E-by-comparison : {n : ℕ} (S : FaceSelection n)
    (η : CubicalNatural (SelectedFaces.complex S) (Nₘ (suc r) H))
    (i j : Position (suc n)) → PositionComparison i j → (a b : Bool)
    → (p : fst (S (i , a))) (q : fst (S (j , b)))
    (x y : Vertex (Grid (suc r) n))
    → insertGrid (suc r) i a x ≡ insertGrid (suc r) j b y
    → onVertices (E (suc r) S η (i , a) p) x
      ≡ onVertices (E (suc r) S η (j , b) q) y
  E-by-comparison S η i .i (same .i) a b p q x y e =
    E-same-position S η i a b p q x y e
  E-by-comparison S η .(lowerWide c) .(upperWide c) (forward c) a b p q x y e =
    E-distinct-face (suc r) S η c a b p q x y e
  E-by-comparison S η .(upperWide c) .(lowerWide c) (backward c) a b p q x y e =
    sym (E-distinct-face (suc r) S η c b a q p y x (sym e))

  -- 主结论：选面证书、坐标和面内点都可以不同；只要它们在环境
  -- 网格中表示同一点，η 的两个评价就相同。H 可在任意宇宙且无限。
  face-point-evaluation : {n : ℕ} (S : FaceSelection n)
    (η : CubicalNatural (SelectedFaces.complex S) (Nₘ (suc r) H))
    (j k : Facet n) (p : fst (S j)) (q : fst (S k))
    (x y : Vertex (Grid (suc r) n))
    → insertGrid (suc r) (fst j) (snd j) x
      ≡ insertGrid (suc r) (fst k) (snd k) y
    → onVertices (E (suc r) S η j p) x ≡ onVertices (E (suc r) S η k q) y
  face-point-evaluation S η (i , a) (j , b) p q x y e =
    E-by-comparison S η i j (comparePositions i j) a b p q x y e
