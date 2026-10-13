{-# OPTIONS --cubical --safe #-}

module DHH.Enrichment.GridCompositionNaturality where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import DHH.Graph
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve
open import DHH.Enrichment.GraphHom
open import DHH.Enrichment.GridComposition
import DHH.Cubical.TensorCategory.Coordinates as C
open import DHH.Cubical.TensorCategory

private variable ℓG ℓH ℓK : Level

-- 输入是两块有限网格坐标和一个阈值。沿第一块的长度递归，证明
-- “先拼接再取阈值”等于“分别取阈值再拼接”。没有枚举网格顶点。
threshold-append-grid : {r : ℕ} (t : Fin r) (p q : ℕ)
  (x : Vertex (Grid r p)) (y : Vertex (Grid r q))
  → thresholdGrid t (p + q) (appendGridPoint r p q x y)
    ≡ C.appendPoint p q (thresholdGrid t p x) (thresholdGrid t q y)
threshold-append-grid t zero q tt y = refl
threshold-append-grid t (suc p) q (a , x) y =
  cong (fst (thresholdGrid t (suc p) (a , x)) ,_) (threshold-append-grid t p q x y)

-- CubicalMap 已经按布尔顶点上的语义等式取商。有限链上取所有严格
-- 阈值能分离坐标，因此布尔分块公式提升到任意有限区间大小 r。
-- 这里使用已有的分离定理，不额外选择 CubeWord 的代表元。
gridAction-tensor-on-append : (r : ℕ) {m n p q : ℕ}
  (f : CubicalMap m n) (g : CubicalMap p q)
  (x : Vertex (Grid r m)) (y : Vertex (Grid r p))
  → onVertices (gridAction r (f ⊗c g)) (appendGridPoint r m p x y)
    ≡ appendGridPoint r n q (onVertices (gridAction r f) x) (onVertices (gridAction r g) y)
gridAction-tensor-on-append r {m} {n} {p} {q} f g x y =
  thresholdGrid-ext (n + q) _ _ λ t →
    gridAction-threshold r (f ⊗c g) t (appendGridPoint r m p x y)
    ∙ cong (onVertices (underlying (f ⊗c g))) (threshold-append-grid t m p x y)
    ∙ tensor-on-append f g (thresholdGrid t m x) (thresholdGrid t p y)
    ∙ cong₂ (C.appendPoint n q)
        (sym (gridAction-threshold r f t x)) (sym (gridAction-threshold r g t y))
    ∙ sym (threshold-append-grid t n q (onVertices (gridAction r f) x) (onVertices (gridAction r g) y))

gridAction-tensor-split : (r : ℕ) {m n p q : ℕ}
  (f : CubicalMap m n) (g : CubicalMap p q) (z : Vertex (Grid r (m + p)))
  → splitGridPoint r n q (onVertices (gridAction r (f ⊗c g)) z)
    ≡ (onVertices (gridAction r f) (fst (splitGridPoint r m p z)) ,
       onVertices (gridAction r g) (snd (splitGridPoint r m p z)))
gridAction-tensor-split r {m} {n} {p} {q} f g z =
  cong (λ w → splitGridPoint r n q (onVertices (gridAction r (f ⊗c g)) w))
    (sym (append-split-grid-point r m p z))
  ∙ cong (splitGridPoint r n q)
      (gridAction-tensor-on-append r f g (fst (splitGridPoint r m p z)) (snd (splitGridPoint r m p z)))
  ∙ split-append-grid-point r n q
      (onVertices (gridAction r f) (fst (splitGridPoint r m p z)))
      (onVertices (gridAction r g) (snd (splitGridPoint r m p z)))

-- 任意两个立方重索引分别作用于两块输入，分块复合与它们交换。
-- 包含面、退化、连接及其任意复合；不是只核对一张生成元表。
composeGrid-reindex : (r : ℕ) {m n p q : ℕ}
  {G : Graph ℓG} {H : Graph ℓH} {K : Graph ℓK}
  (f : CubicalMap m n) (g : CubicalMap p q)
  (a : Cell (Nₘ r (HomGraph H K)) n) (b : Cell (Nₘ r (HomGraph G H)) q)
  → reindex (Nₘ r (HomGraph G K)) (f ⊗c g) (composeGridCells r {p = n} {q = q} a b)
    ≡ composeGridCells r {p = m} {q = p}
      (reindex (Nₘ r (HomGraph H K)) f a) (reindex (Nₘ r (HomGraph G H)) g b)
composeGrid-reindex r f g a b = homExt λ z →
  cong (λ xy → onVertices a (fst xy) ∘g onVertices b (snd xy)) (gridAction-tensor-split r f g z)

-- 结论是有限阶段的真正双次数自然性。它不自动提供稳定余极限的
-- 双变量消去，也不把 Day tensor 等同于预层逐度 Cartesian product。
