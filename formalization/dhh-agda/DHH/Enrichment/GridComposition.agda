{-# OPTIONS --cubical --safe #-}

module DHH.Enrichment.GridComposition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import Cubical.Categories.Category.Base using (CatIso; catiso)
open import DHH.Graph
open import DHH.GraphSets
open import DHH.CubicalNerve
open import DHH.StableNerve.Interval
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Transitions
open import DHH.Enrichment.GraphHom
open import DHH.Enrichment.GraphHomCoherence

private variable ℓG ℓH ℓK : Level

-- 分块只递归第一块长度 p：剥去一个坐标，处理剩余部分，再放回。
-- p=0 时丢弃/加入唯一的零维点。复杂图顶点或所有 cube 无需枚举。
splitGridPoint : (r p q : ℕ) → Vertex (Grid r (p + q))
  → Vertex (Grid r p) × Vertex (Grid r q)
splitGridPoint r zero q x = tt , x
splitGridPoint r (suc p) q (a , x) =
  let yz = splitGridPoint r p q x
  in (a , fst yz) , snd yz

appendGridPoint : (r p q : ℕ) → Vertex (Grid r p) → Vertex (Grid r q)
  → Vertex (Grid r (p + q))
appendGridPoint r zero q x y = y
appendGridPoint r (suc p) q (a , x) y = a , appendGridPoint r p q x y

split-append-grid-point : (r p q : ℕ) (x : Vertex (Grid r p)) (y : Vertex (Grid r q))
  → splitGridPoint r p q (appendGridPoint r p q x y) ≡ (x , y)
split-append-grid-point r zero q tt y = refl
split-append-grid-point r (suc p) q (a , x) y =
  cong (λ yz → (a , fst yz) , snd yz) (split-append-grid-point r p q x y)

append-split-grid-point : (r p q : ℕ) (x : Vertex (Grid r (p + q)))
  → appendGridPoint r p q (fst (splitGridPoint r p q x)) (snd (splitGridPoint r p q x)) ≡ x
append-split-grid-point r zero q x = refl
append-split-grid-point r (suc p) q (a , x) =
  cong (a ,_) (append-split-grid-point r p q x)

-- BOX 结合子的反向也是图映射；证明只逐层处理“哪一坐标变化”。
boxUnassociate : {ℓA ℓB ℓC : Level} (A : Graph ℓA) (B : Graph ℓB) (C : Graph ℓC)
  → Hom (A BOX (B BOX C)) ((A BOX B) BOX C)
onVertices (boxUnassociate A B C) (a , b , c) = (a , b) , c
preserves (boxUnassociate A B C) {x = (a , b , c)} {y = (a' , b' , c')} =
  PT.rec (adj-isProp ((A BOX B) BOX C) ((a , b) , c) ((a' , b') , c')) λ where
  (inl (a , bc)) → PT.rec (adj-isProp ((A BOX B) BOX C) ((a i0 , b) , c) ((a i1 , b') , c'))
    (λ where
      (inl (b , c)) → ∣ inl ((λ i → a i , b i) , c) ∣₁
      (inr (b , c)) → ∣ inr (∣ inl (a , b) ∣₁ , c) ∣₁) bc
  (inr (a , bc)) → ∣ inr (∣ inr (a , cong fst bc) ∣₁ , cong snd bc) ∣₁

splitGridMap : (r p q : ℕ) → Hom (Grid r (p + q)) (Grid r p BOX Grid r q)
onVertices (splitGridMap r p q) = splitGridPoint r p q
preserves (splitGridMap r zero q) e = ∣ inl (refl , e) ∣₁
preserves (splitGridMap r (suc p) q) e = preserves
  (boxUnassociate (Iₘ r) (Grid r p) (Grid r q)
    ∘g boxMap (idHom (Iₘ r)) (splitGridMap r p q)) e

appendGridMap : (r p q : ℕ) → Hom (Grid r p BOX Grid r q) (Grid r (p + q))
onVertices (appendGridMap r p q) (x , y) = appendGridPoint r p q x y
preserves (appendGridMap r zero q) e = preserves (boxLeftUnit (Grid r q)) e
preserves (appendGridMap r (suc p) q) e = preserves
  (boxMap (idHom (Iₘ r)) (appendGridMap r p q)
    ∘g boxAssociate (Iₘ r) (Grid r p) (Grid r q)) e

append-split-grid : (r p q : ℕ)
  → appendGridMap r p q ∘g splitGridMap r p q ≡ idHom (Grid r (p + q))
append-split-grid r p q = homExt (append-split-grid-point r p q)

split-append-grid : (r p q : ℕ)
  → splitGridMap r p q ∘g appendGridMap r p q ≡ idHom (Grid r p BOX Grid r q)
split-append-grid r p q = homExt (λ { (x , y) → split-append-grid-point r p q x y })

gridSplitIso : (r p q : ℕ)
  → CatIso (GraphCategory ℓ-zero) (Grid r (p + q)) (Grid r p BOX Grid r q)
gridSplitIso r p q = catiso (splitGridMap r p q) (appendGridMap r p q)
  (split-append-grid r p q) (append-split-grid r p q)

-- 输出次数是 p+q。两个输入 cube 分别读取前/后两个独立坐标块，
-- 由真实 BOX 图映射确保只有一块的一个坐标变化时仍保持相邻。
-- 绝不把同次数的逐点同步复合当作图映射。
composeGridCells : (r : ℕ) {p q : ℕ}
  {G : Graph ℓG} {H : Graph ℓH} {K : Graph ℓK}
  → Hom (Grid r p) (HomGraph H K) → Hom (Grid r q) (HomGraph G H)
  → Hom (Grid r (p + q)) (HomGraph G K)
composeGridCells r {p} {q} {G} {H} {K} a b =
  compositionGraph {G = G} {H = H} {K = K} ∘g boxMap a b ∘g splitGridMap r p q

composeGrid-on-append : (r : ℕ) {p q : ℕ}
  {G : Graph ℓG} {H : Graph ℓH} {K : Graph ℓK}
  (a : Hom (Grid r p) (HomGraph H K)) (b : Hom (Grid r q) (HomGraph G H))
  (x : Vertex (Grid r p)) (y : Vertex (Grid r q))
  → onVertices (composeGridCells r {p = p} {q = q} a b) (appendGridPoint r p q x y)
    ≡ onVertices a x ∘g onVertices b y
composeGrid-on-append r {p} {q} a b x y =
  cong (λ xy → onVertices a (fst xy) ∘g onVertices b (snd xy))
    (split-append-grid-point r p q x y)

-- 每个坐标采用同一个区间图映射时，分块程序与改变网格大小交换。
-- 因而以下一条递归证明同时覆盖左右端边折叠和所有有限阶段过渡。
mapGrid-split : {r s : ℕ} (M : IntervalMorph r s) (p q : ℕ)
  (x : Vertex (Grid r (p + q)))
  → splitGridPoint s p q (onVertices (mapGrid M (p + q)) x)
    ≡ (onVertices (mapGrid M p) (fst (splitGridPoint r p q x)) ,
       onVertices (mapGrid M q) (snd (splitGridPoint r p q x)))
mapGrid-split M zero q x = refl
mapGrid-split M (suc p) q (a , x) =
  cong (λ yz → (onVertices (intervalMap M) a , fst yz) , snd yz) (mapGrid-split M p q x)

mapGrid-append : {r s : ℕ} (M : IntervalMorph r s) (p q : ℕ)
  (x : Vertex (Grid r p)) (y : Vertex (Grid r q))
  → onVertices (mapGrid M (p + q)) (appendGridPoint r p q x y)
    ≡ appendGridPoint s p q (onVertices (mapGrid M p) x) (onVertices (mapGrid M q) y)
mapGrid-append M zero q x y = refl
mapGrid-append M (suc p) q (a , x) y =
  cong (onVertices (intervalMap M) a ,_) (mapGrid-append M p q x y)

composeGrid-changeSize : {r s : ℕ} (M : IntervalMorph r s) {p q : ℕ}
  {G : Graph ℓG} {H : Graph ℓH} {K : Graph ℓK}
  (a : Hom (Grid s p) (HomGraph H K)) (b : Hom (Grid s q) (HomGraph G H))
  → mapCells (changeSize M (HomGraph G K)) (p + q) (composeGridCells s {p = p} {q = q} a b)
    ≡ composeGridCells r {p = p} {q = q}
      (mapCells (changeSize M (HomGraph H K)) p a)
      (mapCells (changeSize M (HomGraph G H)) q b)
composeGrid-changeSize M {p} {q} a b = homExt λ x →
  cong (λ yz → onVertices a (fst yz) ∘g onVertices b (snd yz)) (mapGrid-split M p q x)

composeGrid-chooseTransition : (which : Bool) (r : ℕ) {p q : ℕ}
  {G : Graph ℓG} {H : Graph ℓH} {K : Graph ℓK}
  (a : Hom (Grid r p) (HomGraph H K)) (b : Hom (Grid r q) (HomGraph G H))
  → mapCells (chooseTransition which r (HomGraph G K)) (p + q) (composeGridCells r {p = p} {q = q} a b)
    ≡ composeGridCells (suc r) {p = p} {q = q}
      (mapCells (chooseTransition which r (HomGraph H K)) p a)
      (mapCells (chooseTransition which r (HomGraph G H)) q b)
composeGrid-chooseTransition true r {p} {q} a b = composeGrid-changeSize (leftMorph r) {p = p} {q = q} a b
composeGrid-chooseTransition false r {p} {q} a b = composeGrid-changeSize (rightMorph r) {p = p} {q = q} a b

composeGrid-stageTransition : (k : ℕ) {p q : ℕ}
  {G : Graph ℓG} {H : Graph ℓH} {K : Graph ℓK}
  (a : Cell (Stage (HomGraph H K) k) p) (b : Cell (Stage (HomGraph G H) k) q)
  → mapCells (stageTransition (HomGraph G K) k) (p + q) (composeGridCells (suc k) {p = p} {q = q} a b)
    ≡ composeGridCells (suc (suc k)) {p = p} {q = q}
      (mapCells (stageTransition (HomGraph H K) k) p a)
      (mapCells (stageTransition (HomGraph G H) k) q b)
composeGrid-stageTransition k {p} {q} a b = composeGrid-chooseTransition (evenStage k) (suc k) {p = p} {q = q} a b

-- 本模块给定有限维输入便构造有限维输出，并证明所有阶段的一致性。
-- N∞ 的双变量降商以及 cubical Day tensor 的普遍性质还需后续证明。
