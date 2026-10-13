{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornFocusedMap where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; snotz; +-zero)
open import Cubical.Data.FinData using (Fin; toℕ)
open import Cubical.Data.Bool using (Bool; false; true; not; true≢false; false≢true)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.Cubes using (Position; here; there)
open import DHH.Cubical.Faces using (Facet)
open import DHH.StableNerve.Interval
open import DHH.StableNerve.Grid using (Grid)
open import DHH.StableNerve.IntegerClamp using (clampNat; clamp-at-or-above)
open import DHH.StableNerve.HornScalar
open import DHH.StableNerve.HornInterval
open import DHH.StableNerve.HornDistance using (windowCoordinate)
open import DHH.StableNerve.HornWindow
open import DHH.StableNerve.HornGridDistance
open import DHH.StableNerve.HornGridEdges

heightMap : (m : ℕ) → Bool → ℕ → Hom (Iₘ m) (Iₘ m)
heightMap m true D = positiveMap m D
heightMap m false D = negativeMap m D

height : (m : ℕ) → Bool → ℕ → Fin (suc m) → Fin (suc m)
height m ε D = onVertices (heightMap m ε D)

height-near-distance : (m : ℕ) (ε : Bool) {D E : ℕ} → NearNat D E
  → (c : Fin (suc m)) → Near (height m ε D c) (height m ε E c)
height-near-distance m true {D} {E} e c = positiveMap-near-distance m {D} {E} e c
height-near-distance m false {D} {E} e c = negativeMap-near-distance m {D} {E} e c

natTop : (m : ℕ) → toℕ (top m) ≡ m
natTop zero = refl
natTop (suc m) = cong suc (natTop m)

clampTop : (m : ℕ) → clampNat m m ≡ top m
clampTop m = cong (clampNat m) (sym (+-zero m)) ∙ clamp-at-or-above m zero

-- D=0 时输出整个反缺面；不是要求所有来源点位于这个面。
height-zero : (m : ℕ) (ε : Bool) (c : Fin (suc m))
  → height m ε zero c ≡ endpoint m (not ε)
height-zero m true c = cong (clampNat m) (positive-zero-distance m (toℕ c) (finite-bound c))
height-zero m false c = cong (clampNat m) (negative-zero-distance m (toℕ c)) ∙ clampTop m

height-opposite : (m D : ℕ) (ε : Bool)
  → height m ε D (endpoint m (not ε)) ≡ endpoint m (not ε)
height-opposite m D true = cong (clampNat m) (positive-opposite-face m D)
height-opposite m D false = cong (clampNat m)
  (cong (negativeHeight m D) (natTop m) ∙ negative-opposite-face m D) ∙ clampTop m

positionTag : {n : ℕ} → Position (suc n) → Bool
positionTag here = false
positionTag (there i) = true

other-selected : {n : ℕ} (i : Position n) (b ε : Bool)
  → Path (Facet n) (there i , b) (here , ε) → Empty.⊥
other-selected i b ε p = true≢false (cong (λ j → positionTag (fst j)) p)

opposite-selected : {n : ℕ} (ε : Bool) → (Path (Facet n) (here , not ε) (here , ε) → Empty.⊥)
opposite-selected false p = true≢false (cong snd p)
opposite-selected true p = false≢true (cong snd p)

SelectedPoint : (m : ℕ) (ε : Bool) (n : ℕ) → Vertex (Grid m (suc n)) → Type₀
SelectedPoint m ε n x = Σ[ j ∈ Facet n ]
  ((j ≡ (here , ε) → Empty.⊥) × (coordinateAt m (fst j) x ≡ endpoint m (snd j)))

SharedSelectedFace : (m : ℕ) (ε : Bool) (n : ℕ)
  → Vertex (Grid m (suc n)) → Vertex (Grid m (suc n)) → Type₀
SharedSelectedFace m ε n x y = Σ[ j ∈ Facet n ]
  ((j ≡ (here , ε) → Empty.⊥) × (coordinateAt m (fst j) x ≡ endpoint m (snd j))
    × (coordinateAt m (fst j) y ≡ endpoint m (snd j)))

liftSharedOther : {m n : ℕ} (ε : Bool) {a b : Fin (suc m)} {x y : Vertex (Grid m n)}
  → CommonEndpoint m n x y → SharedSelectedFace m ε n (a , x) (b , y)
liftSharedOther {n = n} ε (i , b , p , q) = (there i , b) , other-selected {n = n} i b ε , p , q

-- 将特殊坐标暂放在首位。GridFocus 把这个实际程序搬回任意坐标；
-- 三倍长度和维数分别是 r=m+(m+m)、n+1，不把细化误作增加维数。
module Focused (m : ℕ) (ε : Bool) (n : ℕ) where
  r : ℕ
  r = m + (m + m)

  private
    C : Fin (suc r) → Fin (suc m)
    C v = windowCoordinate m m (toℕ v)
    D : Vertex (Grid r n) → ℕ
    D = distanceSum m m r n
    T : Vertex (Grid r n) → Vertex (Grid m n)
    T = onVertices (windowGrid m m r n)

  value : Vertex (Grid r (suc n)) → Vertex (Grid m (suc n))
  value (v , x) = height m ε (D x) (C v) , T x

  -- 根本保边原因是 WindowGridEdge 的两支：D变化时T不变，
  -- T变化时D不变。分别把高度相邻和网格相邻送入 BOX 的一支。
  map : Hom (Grid r (suc n)) (Grid m (suc n))
  onVertices map = value
  preserves map {x = v , x} {y = w , y} = PT.rec (adj-isProp (Grid m (suc n)) _ _) λ where
    (inl (p , e)) → PT.rec (adj-isProp (Grid m (suc n)) _ _)
      (λ where
        (endpointGridEdge q d face) → ∣ inr
          (subst (Near (height m ε (D x) (C v))) (cong (λ z → height m ε (D y) (C z)) p)
            (height-near-distance m ε {D x} {D y} d (C v)) , q) ∣₁
        (stableGridEdge q d face) → ∣ inl (cong₂ (height m ε) q (cong C p) , d) ∣₁)
      (windowGridEdge m m r n e)
    (inr (e , p)) → ∣ inr
      (subst (Near (height m ε (D x) (C v))) (cong (λ t → height m ε t (C w)) (cong D p))
        (preserves (heightMap m ε (D x))
          (coordinate-near m m {toℕ v} {toℕ w} (finite-near-nat {r} {v} {w} e))) , cong T p) ∣₁

  -- 顶点评价采用一个由D的零/后继分支递归取得的选面证书。
  -- 目标图不会参与这个计算；后续证明不同面证书给出相同评价。
  selected-point : (x : Vertex (Grid r (suc n))) → SelectedPoint m ε n (value x)
  selected-point (v , x) = choose (D x) refl
    where
    choose : (d : ℕ) → D x ≡ d → SelectedPoint m ε n (value (v , x))
    choose zero d= = (here , not ε) , opposite-selected {n = n} ε ,
      cong (λ t → height m ε t (C v)) d= ∙ height-zero m ε (C v)
    choose (suc d) d= =
      let result = positiveSum-endpoint m m r n x (λ q → snotz (sym d= ∙ q))
      in (there (fst result) , fst (snd result)) , other-selected {n = n} (fst result) (fst (snd result)) ε , snd (snd result)

  stableShared : (v w : Fin (suc r)) (x y : Vertex (Grid r n))
    → D x ≡ D y
    → ((D x ≡ zero → Empty.⊥) → CommonEndpoint m n (T x) (T y))
    → SharedSelectedFace m ε n (value (v , x)) (value (w , y))
  stableShared v w x y same common = choose (D x) refl
    where
    choose : (d : ℕ) → D x ≡ d → SharedSelectedFace m ε n (value (v , x)) (value (w , y))
    choose zero d= = (here , not ε) , opposite-selected {n = n} ε ,
      (cong (λ t → height m ε t (C v)) d= ∙ height-zero m ε (C v)) ,
      (cong (λ t → height m ε t (C w)) (sym same ∙ d=) ∙ height-zero m ε (C w))
    choose (suc d) d= = liftSharedOther {m = m} {n = n} ε (common (λ q → snotz (sym d= ∙ q)))

  equalTailCommon : (x y : Vertex (Grid r n)) → x ≡ y
    → (D x ≡ zero → Empty.⊥) → CommonEndpoint m n (T x) (T y)
  equalTailCommon x y p nonzero =
    let result = positiveSum-endpoint m m r n x nonzero
        i = fst result
        b = fst (snd result)
        q = snd (snd result)
    in i , b , q , sym (cong (λ z → coordinateAt m i (T z)) p) ∙ q

  -- 这个证明比环境保边更强：一条来源边的两输出位于同一个
  -- 已选面。返回截断存在，最终仅向目标图的邻接命题消去。
  shared-face : {x y : Vertex (Grid r (suc n))} → Adj (Grid r (suc n)) x y
    → ∥ SharedSelectedFace m ε n (value x) (value y) ∥₁
  shared-face {x = v , x} {y = w , y} = PT.rec squash₁ λ where
    (inl (p , e)) → PT.map
      (λ where
        (endpointGridEdge q d face) → liftSharedOther {m = m} {n = n} ε face
        (stableGridEdge q d face) → stableShared v w x y q face)
      (windowGridEdge m m r n e)
    (inr (e , p)) → ∣ stableShared v w x y (cong D p) (equalTailCommon x y p) ∣₁

-- 已给环境图同态、每点选面及每边共同面；尚需选面评价把它送入
-- 真正的horn图，以及逐面边界等式与交替阶段相容。
