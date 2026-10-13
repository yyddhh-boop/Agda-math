{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayTensorCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Monoidal.Base using (TensorStr)
open import DHH.CubicalNerve
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.Cubical.DayUnitLift

-- 张量程序与函子律进入库中的实际 Functor 记录；全部 universe
-- 使用同一个算法。单位显式 Lift，不需要 resizing。
dayTensorFunctor : (ℓ : Level)
  → Functor (CubicalSetCategory ℓ ×C CubicalSetCategory ℓ) (CubicalSetCategory ℓ)
Functor.F-ob (dayTensorFunctor ℓ) (A , B) = DayTensor A B
Functor.F-hom (dayTensorFunctor ℓ) (F , G) = dayMap F G
Functor.F-id (dayTensorFunctor ℓ) {A , B} = dayMap-id A B
Functor.F-seq (dayTensorFunctor ℓ) (F , G) (F' , G') = dayMap-compose F F' G G'

dayTensorStr : (ℓ : Level) → TensorStr (CubicalSetCategory ℓ)
TensorStr.─⊗─ (dayTensorStr ℓ) = dayTensorFunctor ℓ
TensorStr.unit (dayTensorStr ℓ) = DayUnitAt ℓ

-- 单位/结合自然同构、三角及五边形等式的实际证明见 DayUnit、
-- DayAssociator、DayCoherence、DayPentagon、DayUnitLift。
-- MonoidalCategory 完整库包装因复杂记录转换检查超时仍保留在
-- work/dhh 的未验收草稿；本模块只宣称上面已构造的 TensorStr。
