{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.GraphPresentationComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.GraphSets
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve
import DHH.Cubical.FinitePresentation as FP
import DHH.Cubical.GraphPresentation as GP
import DHH.Cubical.GraphCoend as GC
open import DHH.Enrichment.OrderedGraphCodes using (GraphIso)

-- 输入是有限生成维数和有限关系列表；P 的 cell 仍覆盖所有维数。
-- 左边只使用生成节点的网格，右边使用 P 的全部 cell 网格。
-- 两边的边都来自共同生成网格，并非顶点集合的诱导子图。
module Comparison (m r : ℕ) (dim : Fin r → ℕ)
                  (q : ℕ) (relations : Fin q → FP.Relation dim) where
  module P = FP.Presentation r dim q relations
  module F = GP.GraphPresentation m r dim q relations
  module C = GC.GraphCoend m P.complex

  -- 先解释有限节点，再利用全部重索引关系得到整个预层的单位。
  -- 这个过程使用集合商的递归原则，不为商元素选择代表。
  finiteUnit : CubicalNatural P.complex (Nₘ m F.graph)
  finiteUnit = P.Interpret.factor (Nₘ m F.graph) F.nodeGraph F.node-relations

  finiteUnit-on-node : (i : Fin r)
    → mapCells finiteUnit (dim i) (P.nodeCell i) ≡ F.nodeGraph i
  finiteUnit-on-node =
    P.Interpret.factor-on-node (Nₘ m F.graph) F.nodeGraph F.node-relations

  -- 正向把一个节点网格送进它所代表的 cell 网格；反向由有限
  -- 呈示的单位解释全部 cell，分别使用两种图实现的泛性质。
  toCoend : Hom F.graph C.graph
  toCoend = F.fromNerveMap C.graph C.unit

  fromCoend : Hom C.graph F.graph
  fromCoend = C.fromNerveMap F.graph finiteUnit

  toCoend-on-node : (i : Fin r)
    → toCoend ∘g F.nodeGraph i ≡ C.includeGrid (dim i) (P.nodeCell i)
  toCoend-on-node i = homExt (λ _ → refl)

  fromCoend-on-grid : (n : ℕ) (c : Cell P.complex n)
    → fromCoend ∘g C.includeGrid n c ≡ mapCells finiteUnit n c
  fromCoend-on-grid = C.Interpret.factor-on-grid F.graph finiteUnit

  -- 有限图的每个商顶点来自一个节点。单位在该节点的恢复定理
  -- 给出复合为恒等；等式目标为命题，故直接沿商做结构消去。
  from-to : fromCoend ∘g toCoend ≡ idHom F.graph
  from-to = homExt (SQ.elimProp (λ _ → vertex-isSet F.graph _ _)
    (λ { (i , x) → cong (λ h → onVertices h x) (finiteUnit-on-node i) }))

  -- 全余端的生成元是 (n,c,x)。再对 c 的有限呈示商消去后，
  -- c=(i,u)；余端粘接把它精确识别为节点 i 网格中的 u(x)。
  -- 这两层商归纳覆盖全部 cell 维数，不依赖维数或顶点的枚举。
  to-from-on-grid : (n : ℕ) (c : Cell P.complex n) (x : Vertex (Grid m n))
    → onVertices (toCoend ∘g fromCoend) (C.point n c x) ≡ C.point n c x
  to-from-on-grid n = SQ.elimProp
    (λ c → isPropΠ (λ x → vertex-isSet C.graph _ _))
    (λ { (i , u) x → sym (C.identify u (P.nodeCell i) x)
      ∙ cong (λ a → C.point n a x) (P.node-reindex i u) })

  to-from : toCoend ∘g fromCoend ≡ idHom C.graph
  to-from = homExt (SQ.elimProp (λ _ → vertex-isSet C.graph _ _)
    (λ { (n , c , x) → to-from-on-grid n c x }))

  presentationGraphIso : GraphIso F.graph (GC.Γₘ m P.complex)
  GraphIso.forward presentationGraphIso = toCoend
  GraphIso.backward presentationGraphIso = fromCoend
  GraphIso.section presentationGraphIso = to-from
  GraphIso.retraction presentationGraphIso = from-to

  -- GraphIso 在这里仅作为双向保边映射与两逆的记录使用，不输入
  -- 任何良序。此定理识别两种实际图实现，不断言 P→NₘΓₘP
  -- 是弱等价，也不构造稳定 horn 填充或 DHH 的证明。
