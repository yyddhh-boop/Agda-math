{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornGridEdges where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; snotz)
open import Cubical.Data.FinData using (Fin; toℕ)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.Cubes using (Position; here; there)
open import DHH.StableNerve.Interval using (endpoint)
open import DHH.StableNerve.Grid using (Grid)
open import DHH.StableNerve.HornScalar
open import DHH.StableNerve.HornInterval using (finite-near-nat)
open import DHH.StableNerve.HornDistance
open import DHH.StableNerve.HornWindow
open import DHH.StableNerve.HornGridDistance

CommonEndpoint : (b n : ℕ) → Vertex (Grid b n) → Vertex (Grid b n) → Type₀
CommonEndpoint b n x y = Σ[ i ∈ Position n ] Σ[ ε ∈ Bool ]
  (coordinateAt b i x ≡ endpoint b ε) × (coordinateAt b i y ≡ endpoint b ε)

liftCommonTail : {b n : ℕ} {v w : Fin (suc b)} {x y : Vertex (Grid b n)}
  → CommonEndpoint b n x y → CommonEndpoint b (suc n) (v , x) (w , y)
liftCommonTail (i , ε , p , q) = there i , ε , p , q

-- 总距离变化时全部 clamp 坐标不变，并有共同端面。
-- clamp 网格可以变化时总距离不变；若它为正仍给共同端面。
-- 两支正好排除“特殊高度和其它坐标同时改变”的 BOX 障碍。
data WindowGridEdge (a b r n : ℕ) (x y : Vertex (Grid r n)) : Type₀ where
  endpointGridEdge : onVertices (windowGrid a b r n) x ≡ onVertices (windowGrid a b r n) y
    → NearNat (distanceSum a b r n x) (distanceSum a b r n y)
    → CommonEndpoint b n (onVertices (windowGrid a b r n) x) (onVertices (windowGrid a b r n) y)
    → WindowGridEdge a b r n x y
  stableGridEdge : distanceSum a b r n x ≡ distanceSum a b r n y
    → Adj (Grid b n) (onVertices (windowGrid a b r n) x) (onVertices (windowGrid a b r n) y)
    → ((distanceSum a b r n x ≡ zero → Empty.⊥)
        → CommonEndpoint b n (onVertices (windowGrid a b r n) x) (onVertices (windowGrid a b r n) y))
    → WindowGridEdge a b r n x y

module EdgeAt (a b r n : ℕ) (v w : Fin (suc r)) (x y : Vertex (Grid r n)) where
  private
    C : Fin (suc r) → Fin (suc b)
    C z = windowCoordinate a b (toℕ z)
    d : Fin (suc r) → ℕ
    d z = windowDistance a b (toℕ z)
    T : Vertex (Grid r n) → Vertex (Grid b n)
    T = onVertices (windowGrid a b r n)
    S : Vertex (Grid r n) → ℕ
    S = distanceSum a b r n

  fixedHeadCommon : (p : v ≡ w)
    → ((S x ≡ zero → Empty.⊥) → CommonEndpoint b n (T x) (T y))
    → (d v + S x ≡ zero → Empty.⊥)
    → CommonEndpoint b (suc n) (C v , T x) (C w , T y)
  fixedHeadCommon p tailCommon nonzero = choose (d v) refl
    where
    choose : (t : ℕ) → d v ≡ t → CommonEndpoint b (suc n) (C v , T x) (C w , T y)
    choose zero d= = liftCommonTail (tailCommon (λ q → nonzero (cong (_+ S x) d= ∙ q)))
    choose (suc t) d= =
      let result = positive-distance-endpoint a b (toℕ v) (λ q → snotz (sym d= ∙ q))
      in here , fst result , snd result , sym (cong C p) ∙ snd result

  fixedHead : (p : v ≡ w) → WindowGridEdge a b r n x y
    → WindowGridEdge a b r (suc n) (v , x) (w , y)
  fixedHead p (endpointGridEdge q e face) = endpointGridEdge
    (cong₂ _,_ (cong C p) q)
    (subst (λ t → NearNat (d v + S x) (t + S y)) (cong d p)
      (add-near-left (d v) {S x} {S y} e))
    (liftCommonTail face)
  fixedHead p (stableGridEdge q e face) = stableGridEdge
    (cong₂ _+_ (cong d p) q)
    ∣ inl (cong C p , e) ∣₁
    (fixedHeadCommon p face)

  movingHeadCommon : (dv : d v ≡ zero) (p : x ≡ y)
    → (d v + S x ≡ zero → Empty.⊥)
    → CommonEndpoint b (suc n) (C v , T x) (C w , T y)
  movingHeadCommon dv p nonzero =
    let result = positiveSum-endpoint a b r n x
          (λ q → nonzero (cong (_+ S x) dv ∙ q))
        i = fst result
        ε = fst (snd result)
        q = snd (snd result)
    in there i , ε , q , sym (cong (λ z → coordinateAt b i (T z)) p) ∙ q

  movingHead : (p : x ≡ y) → WindowEdge a b (toℕ v) (toℕ w)
    → WindowGridEdge a b r (suc n) (v , x) (w , y)
  movingHead p (leftEdge cv cw e) = endpointGridEdge
    (cong₂ _,_ (cv ∙ sym cw) (cong T p))
    (subst (NearNat (d v + S x)) (cong (d w +_) (cong S p))
      (add-near-right (S x) {d v} {d w} e))
    (here , false , cv , cw)
  movingHead p (rightEdge cv cw e) = endpointGridEdge
    (cong₂ _,_ (cv ∙ sym cw) (cong T p))
    (subst (NearNat (d v + S x)) (cong (d w +_) (cong S p))
      (add-near-right (S x) {d v} {d w} e))
    (here , true , cv , cw)
  movingHead p (middleEdge dv dw e) = stableGridEdge
    (cong (_+ S x) dv ∙ cong S p ∙ sym (cong (_+ S y) dw))
    ∣ inr (e , cong T p) ∣₁
    (movingHeadCommon dv p)

-- 原 BOX 邻接本身是命题截断，因此边分类也只返回截断证书。
-- 下一模块只向邻接命题消去它，不从截断中选一个全局规范面。
windowGridEdge : (a b r n : ℕ) {x y : Vertex (Grid r n)}
  → Adj (Grid r n) x y → ∥ WindowGridEdge a b r n x y ∥₁
windowGridEdge a b r zero {x} {y} e = ∣ stableGridEdge refl tt (λ nonzero → Empty.rec (nonzero refl)) ∣₁
windowGridEdge a b r (suc n) {x = v , x} {y = w , y} = PT.rec squash₁ λ where
  (inl (p , e)) → PT.map (EdgeAt.fixedHead a b r n v w x y p) (windowGridEdge a b r n e)
  (inr (e , p)) → ∣ EdgeAt.movingHead a b r n v w x y p
    (windowEdge a b {toℕ v} {toℕ w} (finite-near-nat {r} {v} {w} e)) ∣₁

-- 这是 Φ 保边和共同面的统一输入。它还不是进入 horn 生成图
-- 的同态；特殊高度与选面评价仍需后续模块实际组合。
