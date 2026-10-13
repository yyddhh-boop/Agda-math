{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.ObjectBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua; uaβ)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Data.Bool using (Bool; false; true; not; notnot; notEquiv; isSetBool; false≢true)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import DHH.Graph

-- 原文用经典“对象集合”，Cubical Agda 的图类型却保留同构路径。
-- 这不是可随手补上的 isSet 字段：下面用两点离散图的置换构造
-- 一个实际非平凡回路，证明 Graph Type₀ 不是集合。
-- 正确后续路线需提供严格对象编码或证明内部模型的比较。
discreteGraph : {ℓ : Level} → hSet ℓ → Graph ℓ
Vertex (discreteGraph A) = fst A
vertex-isSet (discreteGraph A) = snd A
Adj (discreteGraph A) x y = x ≡ y
adj-isProp (discreteGraph A) = snd A
adj-refl (discreteGraph A) x = refl
adj-sym (discreteGraph A) p = sym p

BoolSet : hSet ℓ-zero
BoolSet = Bool , isSetBool

swapSetLoop : BoolSet ≡ BoolSet
swapSetLoop = Σ≡Prop (λ _ → isPropIsSet) (ua notEquiv)

swapGraphLoop : discreteGraph BoolSet ≡ discreteGraph BoolSet
swapGraphLoop = cong discreteGraph swapSetLoop

swap-vertices-path : cong Vertex swapGraphLoop ≡ ua notEquiv
swap-vertices-path = refl

swapGraphLoop-nontrivial : swapGraphLoop ≡ refl → ⊥
swapGraphLoop-nontrivial e = false≢true
  (sym (transportRefl false)
    ∙ sym (cong (λ p → transport (cong Vertex p) false) e)
    ∙ cong (λ p → transport p false) swap-vertices-path
    ∙ uaβ notEquiv false)

Graph₀-not-set : isSet (Graph ℓ-zero) → ⊥
Graph₀-not-set setGraphs = swapGraphLoop-nontrivial
  (setGraphs (discreteGraph BoolSet) (discreteGraph BoolSet) swapGraphLoop refl)

-- 同一个见证可以无resizing地提升到任意图宇宙，特别是旧闭合
-- Concrete.DHH使用的Type₁。不是只在最小宇宙留下的偶然现象。
module AtLevel (ℓ : Level) where
  LiftedBool : hSet ℓ
  LiftedBool = Lift {j = ℓ} Bool , isOfHLevelLift 2 isSetBool

  liftedNotIso : Iso (fst LiftedBool) (fst LiftedBool)
  Iso.fun liftedNotIso b = lift (not (lower b))
  Iso.inv liftedNotIso b = lift (not (lower b))
  Iso.rightInv liftedNotIso b = cong lift (notnot (lower b))
  Iso.leftInv liftedNotIso b = cong lift (notnot (lower b))

  liftedSwap : LiftedBool ≡ LiftedBool
  liftedSwap = Σ≡Prop (λ _ → isPropIsSet) (ua (isoToEquiv liftedNotIso))

  graphLoop : discreteGraph LiftedBool ≡ discreteGraph LiftedBool
  graphLoop = cong discreteGraph liftedSwap

  loop-nontrivial : graphLoop ≡ refl → ⊥
  loop-nontrivial e = false≢true (cong lower
    (sym (transportRefl (lift false))
      ∙ sym (cong (λ p → transport (cong Vertex p) (lift false)) e)
      ∙ uaβ (isoToEquiv liftedNotIso) (lift false)))

  not-set : isSet (Graph ℓ) → ⊥
  not-set h = loop-nontrivial
    (h (discreteGraph LiftedBool) (discreteGraph LiftedBool) graphLoop refl)

Graph-not-set : (ℓ : Level) → isSet (Graph ℓ) → ⊥
Graph-not-set = AtLevel.not-set

-- 不能将物件 Graph Type₀ 的0截断直接充当原图范畴的对象：
-- 态射依赖原对象，截断对象不会自动下降这些 Hom 和复合。
-- 该反例不否定 DHH；它指出将经典 nerve 置于此基础时要付的比较义务。
