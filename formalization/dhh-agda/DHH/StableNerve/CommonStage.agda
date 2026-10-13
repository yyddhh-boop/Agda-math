{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.CommonStage where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Cubical.Data.Nat using (ℕ; zero; suc; max)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; ≤-sucℕ; left-≤-max; right-≤-max)
open import Cubical.Data.Sigma
import Cubical.Relation.Binary.Base as BR
open BR.BinaryRelation using (isEquivRel; equivRel)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
import Cubical.HITs.SetQuotients as SQ
open import DHH.CubicalNerve
open import DHH.StableNerve.StageArithmetic
import DHH.StableNerve.SequenceColimit as SC

private variable ℓ : Level
module CommonStages (A : ℕ → CubicalSet ℓ)
                    (s : (k : ℕ) → CubicalNatural (A k) (A (suc k))) where
  module C = SC.Colimit A s
  module T = Stages A s
  open T public

  -- 一个见证同时包含共同后阶段、两个到达该阶段的比较，以及 cell 的等式。
  -- Common 是它的命题截断；不假称集合商有可计算的规范代表元。
  Witness : (n : ℕ) → C.Tagged n → C.Tagged n → Type ℓ
  Witness n x y = Σ[ M ∈ ℕ ] Σ[ p ∈ fst x ≤ M ] Σ[ q ∈ fst y ≤ M ]
    advanceCell p n (snd x) ≡ advanceCell q n (snd y)

  Common : (n : ℕ) → C.Tagged n → C.Tagged n → Type ℓ
  Common n x y = ∥ Witness n x y ∥₁

  raiseWitness : {n : ℕ} {x y : C.Tagged n} (w : Witness n x y)
    {L : ℕ} → fst w ≤ L → Witness n x y
  raiseWitness {n} {x} {y} (M , p , q , e) {L} r =
    L , ≤-trans p r , ≤-trans q r ,
    (advanceCell-compose p r n (snd x)
      ∙ cong (advanceCell r n) e
      ∙ sym (advanceCell-compose q r n (snd y)))

  common-refl : (n : ℕ) (x : C.Tagged n) → Common n x x
  common-refl n (k , c) = ∣ k , ≤-refl , ≤-refl , refl ∣₁

  common-sym : (n : ℕ) (x y : C.Tagged n) → Common n x y → Common n y x
  common-sym n x y = PT.rec squash₁ (λ { (M , p , q , e) → ∣ M , q , p , sym e ∣₁ })

  common-trans : (n : ℕ) (x y z : C.Tagged n)
    → Common n x y → Common n y z → Common n x z
  common-trans n x y z = PT.rec (isPropΠ (λ _ → squash₁)) λ w1 → PT.rec squash₁ λ w2 →
    let M = max (fst w1) (fst w2)
        a = raiseWitness w1 {L = M} left-≤-max
        b = raiseWitness w2 {L = M} right-≤-max
    in ∣ M , fst (snd a) , fst (snd (snd b)) ,
      (snd (snd (snd a))
        ∙ advanceCell-proof-irrelevant (fst (snd (snd a))) (fst (snd b)) n (snd y)
        ∙ snd (snd (snd b))) ∣₁

  common-equivalence : (n : ℕ) → isEquivRel (Common n)
  common-equivalence n = equivRel (common-refl n) (common-sym n) (common-trans n)

  step-common : (n : ℕ) (x y : C.Tagged n) → C.Step n x y → Common n x y
  step-common n (k , c) .(suc k , mapCells (s k) n c) (C.step c) =
    ∣ suc k , ≤-sucℕ , ≤-refl ,
      (advanceCell-step k n c ∙ sym (advanceCell-id (suc k) n (mapCells (s k) n c))) ∣₁

  -- 正向迭代 include-step，证明过渡任意有限步不改变 colimit 中的点。
  point-later : {k l : ℕ} (p : Later k l) (n : ℕ) (c : Cell (A k) n)
    → C.point n (k , c) ≡ C.point n (l , mapCells (laterMap p) n c)
  point-later now n c = refl
  point-later (next {l} p) n c = point-later p n c
    ∙ SQ.eq/ {R = C.Step n} _ _ (C.step (mapCells (laterMap p) n c))

  point-advance : {k l : ℕ} (p : k ≤ l) (n : ℕ) (c : Cell (A k) n)
    → C.point n (k , c) ≡ C.point n (l , advanceCell p n c)
  point-advance p = point-later (fromLe p)

  common-to-equality : (n : ℕ) (x y : C.Tagged n)
    → Common n x y → C.point n x ≡ C.point n y
  common-to-equality n x y = PT.rec (SQ.squash/ _ _) λ { (M , p , q , e) →
    point-advance p n (snd x) ∙ cong (λ d → C.point n (M , d)) e
      ∙ sym (point-advance q n (snd y)) }

  commonQuotientMap : (n : ℕ) → C.Points n → C.Tagged n SQ./ Common n
  commonQuotientMap n = SQ.rec SQ.squash/ SQ.[_]
    (λ x y r → SQ.eq/ _ _ (step-common n x y r))

  -- 反向不枚举无限步数：先到 Common 商，再使用“命题值等价关系的商有效”。
  -- 得到的是截断存在；这不是共同阶段的可判定搜索算法。
  equality-to-common : (n : ℕ) (x y : C.Tagged n)
    → C.point n x ≡ C.point n y → Common n x y
  equality-to-common n x y p = SQ.effective (λ _ _ → squash₁)
    (common-equivalence n) x y (cong (commonQuotientMap n) p)

  equalityCommonIso : (n : ℕ) (x y : C.Tagged n)
    → Iso (C.point n x ≡ C.point n y) (Common n x y)
  Iso.fun (equalityCommonIso n x y) = equality-to-common n x y
  Iso.inv (equalityCommonIso n x y) = common-to-equality n x y
  Iso.rightInv (equalityCommonIso n x y) p = squash₁ _ p
  Iso.leftInv (equalityCommonIso n x y) p = SQ.squash/ _ _ _ p

  equalityCommonEquivalence : (n : ℕ) (x y : C.Tagged n)
    → (C.point n x ≡ C.point n y) ≃ Common n x y
  equalityCommonEquivalence n x y = isoToEquiv (equalityCommonIso n x y)
