{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.NerveFunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat using (ℕ; suc; _+_)
open import Cubical.Categories.Category.Base using (CatIso; catiso)
open import DHH.Graph
open import DHH.GraphSets
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.Cubical.DayClosed
open import DHH.Cubical.TensorCategory
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Colimit
open import DHH.Enrichment.GraphHom
open import DHH.Enrichment.GraphHomCoherence using (boxMap)
open import DHH.Enrichment.GridComposition
open import DHH.Enrichment.StableComposition

private variable ℓ : Level

-- 把唯一顶点提升到图的宇宙，不增加顶点或额外邻接数据。
-- Hom(P,G) 的常值映射和在唯一顶点的求值给出真正的图同构。
liftPointGraph : (ℓ : Level) → Graph ℓ
Vertex (liftPointGraph ℓ) = Lift {j = ℓ} Unit
vertex-isSet (liftPointGraph ℓ) = isProp→isSet (λ _ _ → refl)
Adj (liftPointGraph ℓ) _ _ = Lift {j = ℓ} Unit
adj-isProp (liftPointGraph ℓ) _ _ _ _ = refl
adj-refl (liftPointGraph ℓ) _ = lift tt
adj-sym (liftPointGraph ℓ) _ = lift tt

constPoint : (G : Graph ℓ) → Hom G (HomGraph (liftPointGraph ℓ) G)
onVertices (constPoint G) x = constantHom G x
preserves (constPoint G) e _ = e

evalPoint : (G : Graph ℓ) → Hom (HomGraph (liftPointGraph ℓ) G) G
onVertices (evalPoint G) f = onVertices f (lift tt)
preserves (evalPoint G) e = e (lift tt)

eval-constPoint : (G : Graph ℓ) → evalPoint G ∘g constPoint G ≡ idHom G
eval-constPoint G = homExt (λ _ → refl)

const-evalPoint : (G : Graph ℓ)
  → constPoint G ∘g evalPoint G ≡ idHom (HomGraph (liftPointGraph ℓ) G)
const-evalPoint G = homExt (λ f → homExt (λ { (lift tt) → refl }))

pointHomIso : (G : Graph ℓ) → CatIso (GraphCategory ℓ) G (HomGraph (liftPointGraph ℓ) G)
pointHomIso G = catiso (constPoint G) (evalPoint G) (const-evalPoint G) (eval-constPoint G)

module _ {ℓ : Level} (G H : Graph ℓ) where
  private
    P : Graph ℓ
    P = liftPointGraph ℓ
    A B C : CubicalSet ℓ
    A = N∞ (HomGraph G H)
    B = N∞ G
    C = N∞ H

    pointInput : CubicalNatural B (N∞ (HomGraph P G))
    pointInput = N∞-map {G = G} {H = HomGraph P G} (constPoint G)

    pointOutput : CubicalNatural (N∞ (HomGraph P H)) C
    pointOutput = N∞-map {G = HomGraph P H} {H = H} (evalPoint H)

  -- 用已降商的稳定复合构造求值，不选择稳定 cell 的阶段代表。
  -- Day 的两块分别容纳映射参数和输入参数，输出维数为 p+q。
  -- 先在配对生成元上给出复合，再用 coend 的 factorDay 降商；
  -- 这也避免检查器重复展开整份稳定复合的商证明字段。
  stableEvaluationPairing : DayPairing A B C
  pairCells stableEvaluationPairing p q a b =
    mapCells {A = N∞ (HomGraph P H)} {B = C} pointOutput (p + q)
      (mergeN∞ P G H p q a (mapCells {A = B} {B = N∞ (HomGraph P G)} pointInput q b))
  pair-natural stableEvaluationPairing {p} {p'} {q} {q'} f g a b =
    cong (λ z → mapCells {A = N∞ (HomGraph P H)} {B = C} pointOutput (p + q)
      (mergeN∞ P G H p q (reindex A f a) z))
      (natural {A = B} {B = N∞ (HomGraph P G)} pointInput g b)
    ∙ cong (mapCells {A = N∞ (HomGraph P H)} {B = C} pointOutput (p + q))
      (mergeN∞-reindex P G H f g a
        (mapCells {A = B} {B = N∞ (HomGraph P G)} pointInput q' b))
    ∙ natural {A = N∞ (HomGraph P H)} {B = C} pointOutput (f ⊗c g)
      (mergeN∞ P G H p' q' a
        (mapCells {A = B} {B = N∞ (HomGraph P G)} pointInput q' b))

  stableEvaluation : CubicalNatural (DayTensor A B) C
  stableEvaluation = factorDay {A = A} {B = B} {C = C} stableEvaluationPairing

  stableEvaluation-β : (p q : ℕ) (a : Cell A p) (b : Cell B q)
    → mapCells {A = DayTensor A B} {B = C} stableEvaluation (p + q)
        (dayPair {A = A} {B = B} p q a b)
      ≡ mapCells {A = N∞ (HomGraph P H)} {B = C} pointOutput (p + q)
        (mergeN∞ P G H p q a (mapCells {A = B} {B = N∞ (HomGraph P G)} pointInput q b))
  stableEvaluation-β = factorDay-β {A = A} {B = B} {C = C} stableEvaluationPairing

  -- 原几何 internal Hom 的实际作用，而不是逐度 Cartesian 指数。
  -- 所有重索引相容性已由 curryDay 的自然变换字段证明。
  nerveHomMap : CubicalNatural A (DayHom B C)
  nerveHomMap = curryDay {C = A} {A = B} {B = C} stableEvaluation

  -- 有限输入程序：把坐标按 p/q 分块，再在图映射上逐点求值。
  -- 分块递归于 p；无需枚举图顶点、全部映射或所有维数。
  evaluateGridCells : (r p q : ℕ)
    → Hom (Grid r p) (HomGraph G H) → Hom (Grid r q) G
    → Hom (Grid r (p + q)) H
  evaluateGridCells r p q a b = evalPoint H ∘g
    composeGridCells r {p = p} {q = q} {G = P} {H = G} {K = H}
      a (constPoint G ∘g b)

  evaluateGrid-on-append : (r p q : ℕ)
    (a : Hom (Grid r p) (HomGraph G H)) (b : Hom (Grid r q) G)
    (x : Vertex (Grid r p)) (y : Vertex (Grid r q))
    → onVertices (evaluateGridCells r p q a b) (appendGridPoint r p q x y)
      ≡ onVertices (onVertices a x) (onVertices b y)
  evaluateGrid-on-append r p q a b x y =
    cong (λ f → onVertices f (lift tt))
      (composeGrid-on-append r {p = p} {q = q} {G = P} {H = G} {K = H}
        a (constPoint G ∘g b) x y)

  evaluateGrid-as-evaluation : (r p q : ℕ)
    (a : Hom (Grid r p) (HomGraph G H)) (b : Hom (Grid r q) G)
    → evaluateGridCells r p q a b
      ≡ evaluationGraph G H ∘g boxMap a b ∘g splitGridMap r p q
  evaluateGrid-as-evaluation r p q a b = homExt (λ _ → refl)

  -- 本模块构造 Hom 上的真实作用及其求值公式。它尚不声称整个
  -- 富集函子的单位/结合图或 Kan 条件已由本模块单独完成。
