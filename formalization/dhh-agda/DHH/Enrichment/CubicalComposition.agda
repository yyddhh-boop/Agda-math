{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.CubicalComposition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; _+_)
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.StableNerve.Interval
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Transitions
open import DHH.Enrichment.GraphHom
open import DHH.Enrichment.GridComposition
open import DHH.Enrichment.GridCompositionNaturality

private variable ℓG ℓH ℓK ℓA ℓB ℓC : Level

-- 由已证明的 coend 唯一性：自然变换在所有双次数配对上相等即可。
dayNaturalExt : {A : CubicalSet ℓA} {B : CubicalSet ℓB} {C : CubicalSet ℓC}
  (F G : CubicalNatural (DayTensor A B) C)
  → ((p q : ℕ) (a : Cell A p) (b : Cell B q)
    → mapCells F (p + q) (dayPair {A = A} {B = B} p q a b)
      ≡ mapCells G (p + q) (dayPair {A = A} {B = B} p q a b))
  → F ≡ G
dayNaturalExt F G e = factorDay-unique (pairFromNatural G) F e
  ∙ sym (factorDay-unique (pairFromNatural G) G (λ _ _ _ _ → refl))

module _ (G : Graph ℓG) (H : Graph ℓH) (K : Graph ℓK) where
  finiteCompositionPairing : (r : ℕ)
    → DayPairing (Nₘ r (HomGraph H K)) (Nₘ r (HomGraph G H)) (Nₘ r (HomGraph G K))
  pairCells (finiteCompositionPairing r) p q = composeGridCells r {p = p} {q = q} {G = G} {H = H} {K = K}
  pair-natural (finiteCompositionPairing r) f g a b = sym (composeGrid-reindex r f g a b)

  -- 有限网格的分块复合已经与任意重索引交换，因此真正降到 Day 商。
  -- 给定 raw 代表时先复合两个网格块，再沿 chart 拉回，完全结构化。
  finiteComposition : (r : ℕ)
    → CubicalNatural (DayTensor (Nₘ r (HomGraph H K)) (Nₘ r (HomGraph G H))) (Nₘ r (HomGraph G K))
  finiteComposition r = factorDay (finiteCompositionPairing r)

  finiteComposition-β : (r p q : ℕ)
    (a : Cell (Nₘ r (HomGraph H K)) p) (b : Cell (Nₘ r (HomGraph G H)) q)
    → mapCells (finiteComposition r) (p + q)
        (dayPair {A = Nₘ r (HomGraph H K)} {B = Nₘ r (HomGraph G H)} p q a b)
      ≡ composeGridCells r {p = p} {q = q} a b
  finiteComposition-β r = factorDay-β (finiteCompositionPairing r)

  finiteComposition-changeSize : {r s : ℕ} (M : IntervalMorph r s)
    → finiteComposition s ⋆n changeSize M (HomGraph G K)
      ≡ dayMap (changeSize M (HomGraph H K)) (changeSize M (HomGraph G H)) ⋆n finiteComposition r
  finiteComposition-changeSize {r} {s} M = dayNaturalExt _ _ λ p q a b →
    cong (mapCells (changeSize M (HomGraph G K)) (p + q)) (finiteComposition-β s p q a b)
    ∙ composeGrid-changeSize M {p = p} {q = q} a b
    ∙ sym (cong (mapCells (finiteComposition r) (p + q))
        (dayMap-β (changeSize M (HomGraph H K)) (changeSize M (HomGraph G H)) p q a b)
      ∙ finiteComposition-β r p q
        (mapCells (changeSize M (HomGraph H K)) p a) (mapCells (changeSize M (HomGraph G H)) q b))

  -- 原始交替左右折叠序列的交换方块是实际自然变换等式。
  finiteComposition-stage : (k : ℕ)
    → finiteComposition (suc k) ⋆n stageTransition (HomGraph G K) k
      ≡ dayMap (stageTransition (HomGraph H K) k) (stageTransition (HomGraph G H) k)
        ⋆n finiteComposition (suc (suc k))
  finiteComposition-stage k = dayNaturalExt _ _ λ p q a b →
    cong (mapCells (stageTransition (HomGraph G K) k) (p + q)) (finiteComposition-β (suc k) p q a b)
    ∙ composeGrid-stageTransition k {p = p} {q = q} a b
    ∙ sym (cong (mapCells (finiteComposition (suc (suc k))) (p + q))
        (dayMap-β (stageTransition (HomGraph H K) k) (stageTransition (HomGraph G H) k) p q a b)
      ∙ finiteComposition-β (suc (suc k)) p q
        (mapCells (stageTransition (HomGraph H K) k) p a) (mapCells (stageTransition (HomGraph G H) k) q b))

-- 本文件处理每个有限阶段及全部过渡；稳定余极限的两变量商消去
-- 是另一项证明，并不由单变量 colimit 的接口自动提供。
