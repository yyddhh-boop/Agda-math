{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornGridDistance where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; snotz)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans; ≤SumLeft; ≤SumRight)
open import Cubical.Data.FinData using (Fin; toℕ)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.Cubes using (Position; here; there)
open import DHH.StableNerve.Interval using (endpoint)
open import DHH.StableNerve.Grid using (Grid; deleteGrid)
open import DHH.StableNerve.HornScalar
open import DHH.StableNerve.HornInterval using (finite-near-nat)
open import DHH.StableNerve.HornDistance
open import DHH.StableNerve.HornWindow

coordinateAt : (r : ℕ) {n : ℕ} → Position n → Vertex (Grid r n) → Fin (suc r)
coordinateAt r here (a , x) = a
coordinateAt r (there i) (a , x) = coordinateAt r i x

-- 距离和按坐标列表递归。输入允许任意网格宽度 r，窗口参数
-- a,b 与维数 n 独立；特别实例 a=b=m、r=3m 给原论文的 D。
distanceSum : (a b r n : ℕ) → Vertex (Grid r n) → ℕ
distanceSum a b r zero x = zero
distanceSum a b r (suc n) (v , x) = windowDistance a b (toℕ v) + distanceSum a b r n x

-- BOX 一条边仅改变一块。相等块经 cong 运输，变化块复用前一
-- 模块的三分支证书。截断只消去到 NearNat 的命题性目标。
distanceSum-near : (a b r n : ℕ) {x y : Vertex (Grid r n)}
  → Adj (Grid r n) x y → NearNat (distanceSum a b r n x) (distanceSum a b r n y)
distanceSum-near a b r zero e = tt
distanceSum-near a b r (suc n) {x = v , x} {y = w , y} =
  PT.rec (nearNat-prop (distanceSum a b r (suc n) (v , x)) (distanceSum a b r (suc n) (w , y))) λ where
    (inl (p , e)) → subst
      (λ d → NearNat (windowDistance a b (toℕ v) + distanceSum a b r n x)
                    (d + distanceSum a b r n y))
      (cong (λ z → windowDistance a b (toℕ z)) p)
      (add-near-left (windowDistance a b (toℕ v))
        {distanceSum a b r n x} {distanceSum a b r n y} (distanceSum-near a b r n e))
    (inr (e , p)) → subst
      (NearNat (windowDistance a b (toℕ v) + distanceSum a b r n x))
      (cong (windowDistance a b (toℕ w) +_) (cong (distanceSum a b r n) p))
      (add-near-right (distanceSum a b r n x)
        {windowDistance a b (toℕ v)} {windowDistance a b (toℕ w)}
        (distance-near a b {toℕ v} {toℕ w} (finite-near-nat {r} {v} {w} e)))

distanceSum-zero : (a b r n : ℕ) (x : Vertex (Grid r n))
  → ((i : Position n) → windowDistance a b (toℕ (coordinateAt r i x)) ≡ zero)
  → distanceSum a b r n x ≡ zero
distanceSum-zero a b r zero x all = refl
distanceSum-zero a b r (suc n) (v , x) all =
  cong₂ _+_ (all here) (distanceSum-zero a b r n x (λ i → all (there i)))

distanceSum-cong : (a b r n : ℕ) (x y : Vertex (Grid r n))
  → ((i : Position n) → windowDistance a b (toℕ (coordinateAt r i x))
                      ≡ windowDistance a b (toℕ (coordinateAt r i y)))
  → distanceSum a b r n x ≡ distanceSum a b r n y
distanceSum-cong a b r zero x y all = refl
distanceSum-cong a b r (suc n) (v , x) (w , y) all =
  cong₂ _+_ (all here) (distanceSum-cong a b r n x y (λ i → all (there i)))

-- 总和非零时，按头距离为0/后继递归返回一个正距离坐标。
-- 这是一份实际有限证书，无须为截断的商点选择代表或做 argmax。
positiveSum-coordinate : (a b r n : ℕ) (x : Vertex (Grid r n))
  → (distanceSum a b r n x ≡ zero → Empty.⊥)
  → Σ[ i ∈ Position n ] (windowDistance a b (toℕ (coordinateAt r i x)) ≡ zero → Empty.⊥)
positiveSum-coordinate a b r zero x nonzero = Empty.rec (nonzero refl)
positiveSum-coordinate a b r (suc n) (v , x) nonzero = choose (windowDistance a b (toℕ v)) refl
  where
  choose : (d : ℕ) → windowDistance a b (toℕ v) ≡ d
    → Σ[ i ∈ Position (suc n) ]
        (windowDistance a b (toℕ (coordinateAt r i (v , x))) ≡ zero → Empty.⊥)
  choose zero d= =
    let result = positiveSum-coordinate a b r n x
          (λ p → nonzero (cong (_+ distanceSum a b r n x) d= ∙ p))
    in there (fst result) , snd result
  choose (suc d) d= = here , (λ p → snotz (sym d= ∙ p))

-- 任一距离加数被总和控制。外端面贡献m，继而得到D≥m；
-- 总和本身可以大于m，不强迫“其它坐标都在中间窗口”。
coordinateDistance-bound : (a b r : ℕ) {n : ℕ} (i : Position n) (x : Vertex (Grid r n))
  → windowDistance a b (toℕ (coordinateAt r i x)) ≤ distanceSum a b r n x
coordinateDistance-bound a b r here (v , x) = ≤SumLeft
coordinateDistance-bound a b r (there i) (v , x) =
  ≤-trans (coordinateDistance-bound a b r i x) ≤SumRight

coordinateAt-window : (a b r : ℕ) {n : ℕ} (i : Position n) (x : Vertex (Grid r n))
  → coordinateAt b i (onVertices (windowGrid a b r n) x)
    ≡ windowCoordinate a b (toℕ (coordinateAt r i x))
coordinateAt-window a b r here (v , x) = refl
coordinateAt-window a b r (there i) (v , x) = coordinateAt-window a b r i x

EndpointWitness : (b n : ℕ) → Vertex (Grid b n) → Type₀
EndpointWitness b n x = Σ[ i ∈ Position n ] Σ[ ε ∈ Bool ] coordinateAt b i x ≡ endpoint b ε

positiveSum-endpoint : (a b r n : ℕ) (x : Vertex (Grid r n))
  → (distanceSum a b r n x ≡ zero → Empty.⊥)
  → EndpointWitness b n (onVertices (windowGrid a b r n) x)
positiveSum-endpoint a b r n x nonzero =
  let result = positiveSum-coordinate a b r n x nonzero
      i = fst result
      endpointResult = positive-distance-endpoint a b (toℕ (coordinateAt r i x)) (snd result)
  in i , fst endpointResult , coordinateAt-window a b r i x ∙ snd endpointResult

-- 缺面方向i的距离排除特殊坐标，直接使用已有实际 gridDelete。
distanceExcept : (a b r : ℕ) {n : ℕ} → Position (suc n) → Vertex (Grid r (suc n)) → ℕ
distanceExcept a b r {n} i x = distanceSum a b r n (deleteGrid r i x)

-- 本模块提供任意维度的距离/端面见证；完整Φ仍需证明变化坐标
-- 与这一共同选面相容，并将环境点的面表示映到实际horn生成图。
