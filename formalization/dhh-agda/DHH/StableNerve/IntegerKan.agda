{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.IntegerKan where

open import Cubical.Foundations.Prelude
open import DHH.Graph
open import DHH.Cubical.Kan
open import DHH.Cubical.KanTransport
open import DHH.StableNerve.Colimit using (N∞)
open import DHH.StableNerve.HornFilling using (N∞-Kan)
open import DHH.StableNerve.IntegerCubical

-- 此证明接上已经证明的完整预层自然同构，而非仅逐度的 cell Iso。
-- transportedIntegerNerve 只是中间比较模型；它的 Kan 性同时可用。
transportedIntegerNerve-Kan : {ℓ : Level} (G : Graph ℓ)
  → IsKan (transportedIntegerNerve G)
transportedIntegerNerve-Kan G = kanAlongNaturalIso
  (toInteger G) (fromInteger G)
  (Transported.from-to G) (Transported.to-from G) (N∞-Kan G)

-- 原文实际整数稳定 nerve 的 cells 是 PaperIntegerCell：
-- 图映射 IntegerGrid n → G，逐坐标、逐符号的最终常值性；
-- faces 是已独立定义的稳定端点，degeneracies 删除坐标，
-- connections 为整数 min/max。IntegerCubical 已识别全部操作
-- 并证明自然同构的两个逆式；这里只运输已经检查的 Kan 证明。
directIntegerNerve-Kan : {ℓ : Level} (G : Graph ℓ)
  → IsKan (directIntegerNerve G)
directIntegerNerve-Kan G = kanAlongNaturalIso
  (integerNerveComparison G) (integerNerveComparisonInverse G)
  (integerNerveComparison-left G) (integerNerveComparison-right G)
  (N∞-Kan G)

-- 任意 universe、包括无限图、全部维数和任意缺面；仍为普通
-- IsKan 的截断存在性，不添加 ChosenKanFillings 或选择公理。
-- 这不证明 N₁→N∞ 的弱等价或原 DHH 的局部化比较。
