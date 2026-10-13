{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornFocusedBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.FinData using (Fin; toℕ)
open import Cubical.Data.Bool using (Bool; false; true; not)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
open import DHH.Graph
open import DHH.Cubes using (Position; here; there)
open import DHH.Cubical.Faces using (Facet)
open import DHH.StableNerve.Interval using (Iₘ; endpoint)
open import DHH.StableNerve.Grid using (Grid; insertGrid; gridFace)
open import DHH.StableNerve.Transitions using (map-insert)
open import DHH.StableNerve.Padding using (middleCollapse; middleGrid)
open import DHH.StableNerve.HornInterval using
  (positiveMap-large-distance; negativeMap-large-distance)
open import DHH.StableNerve.HornDistance using
  (windowCoordinate; windowDistance; coordinate-zero; coordinate-right;
   distance-zero-input; distance-right)
open import DHH.StableNerve.HornWindow using
  (windowGrid; middle-grid-value)
open import DHH.StableNerve.HornGridDistance using
  (coordinateAt; distanceSum; coordinateDistance-bound)
open import DHH.StableNerve.HornFocusedMap

-- 三倍区间的两个外端点都压到对应端点，而其窗口外距离恰为 m。
-- 距离总和无须等于 m：其他坐标仍可贡献任意非负距离。
window-outer-coordinate : (m : ℕ) (b : Bool)
  → windowCoordinate m m (toℕ (endpoint (m + (m + m)) b))
    ≡ endpoint m b
window-outer-coordinate m false = coordinate-zero m m
window-outer-coordinate m true =
  cong (windowCoordinate m m) (natTop (m + (m + m)))
  ∙ coordinate-right m m m

window-outer-distance : (m : ℕ) (b : Bool)
  → windowDistance m m (toℕ (endpoint (m + (m + m)) b)) ≡ m
window-outer-distance m false = distance-zero-input m m
window-outer-distance m true =
  cong (windowDistance m m) (natTop (m + (m + m)))
  ∙ distance-right m m m

outer-coordinate-distance-bound : (m : ℕ) {n : ℕ}
  (i : Position n) (b : Bool) (x : Vertex (Grid (m + (m + m)) n))
  → coordinateAt (m + (m + m)) i x ≡ endpoint (m + (m + m)) b
  → m ≤ distanceSum m m (m + (m + m)) n x
outer-coordinate-distance-bound m {n} i b x outer =
  subst (λ d → d ≤ distanceSum m m (m + (m + m)) n x)
    (cong (λ v → windowDistance m m (toℕ v)) outer
     ∙ window-outer-distance m b)
    (coordinateDistance-bound m m (m + (m + m)) {n = n} i x)

height-large-distance : (m : ℕ) (ε : Bool) (D : ℕ)
  → m ≤ D → (c : Fin (suc m)) → height m ε D c ≡ c
height-large-distance m true D far c =
  cong (λ h → onVertices h c) (positiveMap-large-distance m D far)
height-large-distance m false D far c =
  cong (λ h → onVertices h c) (negativeMap-large-distance m D far)

-- 首坐标的选面只能是反缺面；这是 Bool 的分支证明，即使 m=0
-- 也不需要断言区间的两个端点不同。
selected-first-side : {n : ℕ} (b ε : Bool)
  → (Path (Facet n) (here , b) (here , ε) → Empty.⊥)
  → b ≡ not ε
selected-first-side false false excluded = Empty.rec (excluded refl)
selected-first-side false true excluded = refl
selected-first-side true false excluded = refl
selected-first-side true true excluded = Empty.rec (excluded refl)

-- 在任何已选的来源外端面上，Focused.value 与逐坐标窗口压缩相等。
-- 首坐标用 height-opposite；其他坐标只用 D≥m，绝不假设 D=m。
focused-on-selected-face : (m : ℕ) (ε : Bool) (n : ℕ)
  (j : Facet n)
  → (j ≡ (here , ε) → Empty.⊥)
  → (x : Vertex (Grid (m + (m + m)) (suc n)))
  → coordinateAt (m + (m + m)) (fst j) x
    ≡ endpoint (m + (m + m)) (snd j)
  → Focused.value m ε n x
    ≡ onVertices (windowGrid m m (m + (m + m)) (suc n)) x
focused-on-selected-face m ε n (here , b) excluded (v , x) outer =
  cong (λ c → c , onVertices (windowGrid m m (m + (m + m)) n) x)
    (cong (height m ε (distanceSum m m (m + (m + m)) n x)) q
     ∙ height-opposite m (distanceSum m m (m + (m + m)) n x) ε
     ∙ sym q)
  where
  q : windowCoordinate m m (toℕ v) ≡ endpoint m (not ε)
  q = cong (λ w → windowCoordinate m m (toℕ w)) outer
    ∙ window-outer-coordinate m b
    ∙ cong (endpoint m) (selected-first-side {n = n} b ε excluded)
focused-on-selected-face m ε n (there i , b) excluded (v , x) outer =
  cong (λ c → c , onVertices (windowGrid m m (m + (m + m)) n) x)
    (height-large-distance m ε (distanceSum m m (m + (m + m)) n x)
      (outer-coordinate-distance-bound m {n = n} i b x outer)
      (windowCoordinate m m (toℕ v)))

value-on-selected : (m : ℕ) (ε : Bool) (n : ℕ)
  (z : Vertex (Grid (m + (m + m)) (suc n)))
  (j : Facet n)
  → (j ≡ (here , ε) → Empty.⊥)
  → coordinateAt (m + (m + m)) (fst j) z
    ≡ endpoint (m + (m + m)) (snd j)
  → Focused.value m ε n z
    ≡ onVertices (windowGrid m m (m + (m + m)) (suc n)) z
value-on-selected m ε n z j excluded outer =
  focused-on-selected-face m ε n j excluded z outer

coordinateAt-insert-endpoint : (r : ℕ) {n : ℕ}
  (i : Position (suc n)) (b : Bool) (x : Vertex (Grid r n))
  → coordinateAt r i (insertGrid r i b x) ≡ endpoint r b
coordinateAt-insert-endpoint r here b x = refl
coordinateAt-insert-endpoint r {suc n} (there i) b (a , x) =
  coordinateAt-insert-endpoint r {n = n} i b x

-- 端面等式由已经证过的 middleCollapse 自然性运输到窗口算式。
window-insert-outer : (m : ℕ) {n : ℕ} (i : Position (suc n))
  (b : Bool) (x : Vertex (Grid (m + (m + m)) n))
  → onVertices (windowGrid m m (m + (m + m)) (suc n))
      (insertGrid (m + (m + m)) i b x)
    ≡ insertGrid m i b
      (onVertices (windowGrid m m (m + (m + m)) n) x)
window-insert-outer m {n} i b x =
  sym (middle-grid-value m (suc n) (insertGrid (m + (m + m)) i b x))
  ∙ map-insert (middleCollapse m) {n = n} i b x
  ∙ cong (insertGrid m i b) (middle-grid-value m n x)

focused-selected-face-value : (m : ℕ) (ε : Bool) (n : ℕ)
  (j : Facet n) (excluded : j ≡ (here , ε) → Empty.⊥)
  (x : Vertex (Grid (m + (m + m)) n))
  → Focused.value m ε n
      (insertGrid (m + (m + m)) (fst j) (snd j) x)
    ≡ insertGrid m (fst j) (snd j) (onVertices (middleGrid m n) x)
focused-selected-face-value m ε n j excluded x =
  focused-on-selected-face m ε n j excluded
    (insertGrid (m + (m + m)) (fst j) (snd j) x)
    (coordinateAt-insert-endpoint (m + (m + m)) {n = n} (fst j) (snd j) x)
  ∙ sym (middle-grid-value m (suc n)
      (insertGrid (m + (m + m)) (fst j) (snd j) x))
  ∙ map-insert (middleCollapse m) {n = n} (fst j) (snd j) x

-- 完整 Hom 等式，包含已经构造的保边证明；不是仅逐顶点测试。
focused-selected-boundary : (m : ℕ) (ε : Bool) (n : ℕ)
  (j : Facet n) (excluded : j ≡ (here , ε) → Empty.⊥)
  → Focused.map m ε n
      ∘g gridFace (m + (m + m)) (fst j) (snd j)
    ≡ gridFace m (fst j) (snd j) ∘g middleGrid m n
focused-selected-boundary m ε n j excluded =
  homExt (focused-selected-face-value m ε n j excluded)

focused-selected-window-boundary : (m : ℕ) (ε : Bool) (n : ℕ)
  (j : Facet n) (excluded : j ≡ (here , ε) → Empty.⊥)
  → Focused.map m ε n
      ∘g gridFace (m + (m + m)) (fst j) (snd j)
    ≡ gridFace m (fst j) (snd j)
      ∘g windowGrid m m (m + (m + m)) n
focused-selected-window-boundary m ε n j excluded = homExt λ x →
  focused-on-selected-face m ε n j excluded
    (insertGrid (m + (m + m)) (fst j) (snd j) x)
    (coordinateAt-insert-endpoint (m + (m + m)) {n = n} (fst j) (snd j) x)
  ∙ window-insert-outer m {n = n} (fst j) (snd j) x
