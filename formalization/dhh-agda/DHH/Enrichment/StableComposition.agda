{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.StableComposition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; _+_; max)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; ≤-sucℕ; left-≤-max; right-≤-max)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.DayTensor
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.StageArithmetic
open import DHH.StableNerve.CommonStage
open import DHH.StableNerve.Colimit
open import DHH.Enrichment.GraphHom
open import DHH.Enrichment.GridComposition
open import DHH.Enrichment.GridCompositionNaturality

private variable ℓ : Level

module _ (G H K : Graph ℓ) where
  private
    A = HomGraph H K
    B = HomGraph G H
    C = HomGraph G K
    module AS = CommonStages (Stage A) (stageTransition A)
    module BS = CommonStages (Stage B) (stageTransition B)
    module CS = CommonStages (Stage C) (stageTransition C)

  combineAt : (k p q : ℕ) → Cell (Stage A k) p → Cell (Stage B k) q → Cell (Stage C k) (p + q)
  combineAt k p q = composeGridCells (suc k) {p = p} {q = q} {G = G} {H = H} {K = K}

  -- Later 的有限步数证书直接控制递归。now 为基例，next 使用已经
  -- 证明的一步过渡方块；没有搜索能使两个 cell 相等的阶段。
  combine-later : {k l : ℕ} (t : Later k l) (p q : ℕ)
    (a : Cell (Stage A k) p) (b : Cell (Stage B k) q)
    → mapCells (CS.laterMap t) (p + q) (combineAt k p q a b)
      ≡ combineAt l p q (mapCells (AS.laterMap t) p a) (mapCells (BS.laterMap t) q b)
  combine-later now p q a b = refl
  combine-later (next {l} t) p q a b =
    cong (mapCells (stageTransition C l) (p + q)) (combine-later t p q a b)
    ∙ composeGrid-stageTransition l {p = p} {q = q}
      (mapCells (AS.laterMap t) p a) (mapCells (BS.laterMap t) q b)

  combine-advance : {k l : ℕ} (t : k ≤ l) (p q : ℕ)
    (a : Cell (Stage A k) p) (b : Cell (Stage B k) q)
    → CS.advanceCell t (p + q) (combineAt k p q a b)
      ≡ combineAt l p q (AS.advanceCell t p a) (BS.advanceCell t q b)
  combine-advance t = combine-later (fromLe t)

  pairAt : (p q : ℕ) {k l : ℕ} (M : ℕ) → k ≤ M → l ≤ M
    → Cell (Stage A k) p → Cell (Stage B l) q → Cell (N∞ C) (p + q)
  pairAt p q M h i a b = Stable.point C (p + q)
    (M , combineAt M p q (AS.advanceCell h p a) (BS.advanceCell i q b))

  pairAt-proofs : (p q : ℕ) {k l : ℕ} (M : ℕ) (h h' : k ≤ M) (i i' : l ≤ M)
    (a : Cell (Stage A k) p) (b : Cell (Stage B l) q)
    → pairAt p q M h i a b ≡ pairAt p q M h' i' a b
  pairAt-proofs p q M h h' i i' a b =
    cong₂ (λ x y → Stable.point C (p + q) (M , combineAt M p q x y))
      (AS.advanceCell-proof-irrelevant h h' p a) (BS.advanceCell-proof-irrelevant i i' q b)

  pairAt-raise : (p q : ℕ) {k l M L : ℕ} (h : k ≤ M) (i : l ≤ M) (t : M ≤ L)
    (a : Cell (Stage A k) p) (b : Cell (Stage B l) q)
    → pairAt p q M h i a b ≡ pairAt p q L (≤-trans h t) (≤-trans i t) a b
  pairAt-raise p q {M = M} {L} h i t a b =
    CS.point-advance t (p + q) (combineAt M p q (AS.advanceCell h p a) (BS.advanceCell i q b))
    ∙ cong (λ c → Stable.point C (p + q) (L , c))
      (combine-advance t p q (AS.advanceCell h p a) (BS.advanceCell i q b)
      ∙ cong₂ (combineAt L p q)
        (sym (AS.advanceCell-compose h t p a)) (sym (BS.advanceCell-compose i t q b)))

  -- 两个不同共同阶段升到 max 后逐项相等，所以输出与同步阶段选择
  -- 无关。这里构造的是商中等式，未宣称带阶段表示有规范形式。
  pairAt-independent : (p q : ℕ) {k l : ℕ} (M N : ℕ)
    (h : k ≤ M) (i : l ≤ M) (h' : k ≤ N) (i' : l ≤ N)
    (a : Cell (Stage A k) p) (b : Cell (Stage B l) q)
    → pairAt p q M h i a b ≡ pairAt p q N h' i' a b
  pairAt-independent p q M N h i h' i' a b =
    pairAt-raise p q h i (left-≤-max {m = M} {n = N}) a b
    ∙ pairAt-proofs p q (max M N)
      (≤-trans h left-≤-max) (≤-trans h' right-≤-max)
      (≤-trans i left-≤-max) (≤-trans i' right-≤-max) a b
    ∙ sym (pairAt-raise p q h' i' (right-≤-max {n = N} {m = M}) a b)

  pairAt-left-step : (p q : ℕ) {k l M : ℕ} (h : suc k ≤ M) (i : l ≤ M)
    (a : Cell (Stage A k) p) (b : Cell (Stage B l) q)
    → pairAt p q M (≤-trans ≤-sucℕ h) i a b
      ≡ pairAt p q M h i (mapCells (stageTransition A k) p a) b
  pairAt-left-step p q {k} {M = M} h i a b =
    cong (λ x → Stable.point C (p + q) (M , combineAt M p q x (BS.advanceCell i q b)))
      (AS.advanceCell-compose ≤-sucℕ h p a ∙ cong (AS.advanceCell h p) (AS.advanceCell-step k p a))

  pairAt-right-step : (p q : ℕ) {k l M : ℕ} (h : k ≤ M) (i : suc l ≤ M)
    (a : Cell (Stage A k) p) (b : Cell (Stage B l) q)
    → pairAt p q M h (≤-trans ≤-sucℕ i) a b
      ≡ pairAt p q M h i a (mapCells (stageTransition B l) q b)
  pairAt-right-step p q {l = l} {M = M} h i a b =
    cong (λ y → Stable.point C (p + q) (M , combineAt M p q (AS.advanceCell h p a) y))
      (BS.advanceCell-compose ≤-sucℕ i q b ∙ cong (BS.advanceCell i q) (BS.advanceCell-step l q b))

  mergeTagged : (p q : ℕ) → Stable.Tagged A p → Stable.Tagged B q → Cell (N∞ C) (p + q)
  mergeTagged p q (k , a) (l , b) = pairAt p q (max k l) left-≤-max right-≤-max a b

  mergeTagged-left : (p q : ℕ) (x x' : Stable.Tagged A p) (y : Stable.Tagged B q)
    → Stable.Step A p x x' → mergeTagged p q x y ≡ mergeTagged p q x' y
  mergeTagged-left p q _ _ (l , b) (Stable.step {k = k} a) =
    pairAt-independent p q {k = k} {l = l} (max k l) (max (suc k) l)
      (left-≤-max {m = k} {n = l}) (right-≤-max {n = l} {m = k})
      (≤-trans (≤-sucℕ {n = k}) (left-≤-max {m = suc k} {n = l}))
      (right-≤-max {n = l} {m = suc k}) a b
    ∙ pairAt-left-step p q {k = k} {l = l} {M = max (suc k) l}
      (left-≤-max {m = suc k} {n = l}) (right-≤-max {n = l} {m = suc k}) a b

  mergeTagged-right : (p q : ℕ) (x : Stable.Tagged A p) (y y' : Stable.Tagged B q)
    → Stable.Step B q y y' → mergeTagged p q x y ≡ mergeTagged p q x y'
  mergeTagged-right p q (k , a) _ _ (Stable.step {k = l} b) =
    pairAt-independent p q {k = k} {l = l} (max k l) (max k (suc l))
      (left-≤-max {m = k} {n = l}) (right-≤-max {n = l} {m = k})
      (left-≤-max {m = k} {n = suc l})
      (≤-trans (≤-sucℕ {n = l}) (right-≤-max {n = suc l} {m = k})) a b
    ∙ pairAt-right-step p q {k = k} {l = l} {M = max k (suc l)}
      (left-≤-max {m = k} {n = suc l}) (right-≤-max {n = suc l} {m = k}) a b

  -- 真正的两变量商消去：左右每个生成关系均已单独验证，目标为集合。
  -- SQ.rec2 不选取稳定 cell 的代表，也不要求可数选择或相等可判定。
  mergeN∞ : (p q : ℕ) → Cell (N∞ A) p → Cell (N∞ B) q → Cell (N∞ C) (p + q)
  mergeN∞ p q = SQ.rec2 SQ.squash/ (mergeTagged p q) (mergeTagged-left p q) (mergeTagged-right p q)

  mergeN∞-same-stage : (k p q : ℕ) (a : Cell (Stage A k) p) (b : Cell (Stage B k) q)
    → mergeN∞ p q (mapCells (includeStage A k) p a) (mapCells (includeStage B k) q b)
      ≡ mapCells (includeStage C k) (p + q) (combineAt k p q a b)
  mergeN∞-same-stage k p q a b =
    pairAt-independent p q (max k k) k left-≤-max right-≤-max ≤-refl ≤-refl a b
    ∙ cong₂ (λ x y → Stable.point C (p + q) (k , combineAt k p q x y))
      (AS.advanceCell-id k p a) (BS.advanceCell-id k q b)

  pairAt-reindex : {p p' q q' k l : ℕ} (f : CubicalMap p p') (g : CubicalMap q q')
    (M : ℕ) (h : k ≤ M) (i : l ≤ M) (a : Cell (Stage A k) p') (b : Cell (Stage B l) q')
    → pairAt p q M h i (reindex (Stage A k) f a) (reindex (Stage B l) g b)
      ≡ reindex (N∞ C) (f ⊗c g) (pairAt p' q' M h i a b)
  pairAt-reindex {p} {p'} {q} {q'} f g M h i a b =
    cong (λ c → Stable.point C (p + q) (M , c))
      (cong₂ (combineAt M p q) (natural (AS.advance h) f a) (natural (BS.advance i) g b)
      ∙ sym (composeGrid-reindex (suc M) f g (AS.advanceCell h p' a) (BS.advanceCell i q' b)))

  mergeN∞-reindex : {p p' q q' : ℕ} (f : CubicalMap p p') (g : CubicalMap q q')
    (a : Cell (N∞ A) p') (b : Cell (N∞ B) q')
    → mergeN∞ p q (reindex (N∞ A) f a) (reindex (N∞ B) g b)
      ≡ reindex (N∞ C) (f ⊗c g) (mergeN∞ p' q' a b)
  mergeN∞-reindex f g = SQ.elimProp2 (λ _ _ → SQ.squash/ _ _)
    (λ { (k , a) (l , b) → pairAt-reindex f g (max k l) left-≤-max right-≤-max a b })

  stableCompositionPairing : DayPairing (N∞ A) (N∞ B) (N∞ C)
  pairCells stableCompositionPairing = mergeN∞
  pair-natural stableCompositionPairing = mergeN∞-reindex

  stableComposition : CubicalNatural (DayTensor (N∞ A) (N∞ B)) (N∞ C)
  stableComposition = factorDay stableCompositionPairing

  stableComposition-β : (p q : ℕ) (a : Cell (N∞ A) p) (b : Cell (N∞ B) q)
    → mapCells stableComposition (p + q) (dayPair {A = N∞ A} {B = N∞ B} p q a b) ≡ mergeN∞ p q a b
  stableComposition-β = factorDay-β stableCompositionPairing

  -- 已构造 CK 原图 Hom 的稳定立方复合及 Day 降商。单位/结合律还需
  -- 与实际张量单位子/结合子同域比较；本文件不把它们当作隐藏字段。
