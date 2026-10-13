{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.FiniteStages where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; max)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans; left-≤-max; right-≤-max)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
import Cubical.HITs.SetQuotients as SQ
open import DHH.CubicalNerve
open import DHH.StableNerve.CommonStage
import DHH.StableNerve.SequenceColimit as SC

private variable ℓ : Level
module FiniteFamilies (A : ℕ → CubicalSet ℓ)
                      (s : (k : ℕ) → CubicalNatural (A k) (A (suc k))) where
  module C = SC.Colimit A s
  module K = CommonStages A s
  open K using (advanceCell; point-advance)

  -- 给定显式带阶段代表元，这是可直接运行的有限递归：取阶段的 max。
  -- 这一步输出真正的数据，既不用命题截断，也不用选择公理。
  finiteBound : {n : ℕ} (r : ℕ) (xs : Fin r → C.Tagged n)
    → Σ[ M ∈ ℕ ] ((i : Fin r) → fst (xs i) ≤ M)
  finiteBound zero xs = zero , (λ ())
  finiteBound (suc r) xs =
    let b = finiteBound r (λ i → xs (fsuc i))
        M = max (fst (xs fzero)) (fst b)
    in M , λ where
      fzero → left-≤-max
      (fsuc i) → ≤-trans (snd b i) right-≤-max

  TaggedRepresentation : (n r : ℕ) → (Fin r → C.Tagged n) → Type ℓ
  TaggedRepresentation n r xs = Σ[ M ∈ ℕ ] Σ[ cs ∈ (Fin r → Cell (A M) n) ]
    ((i : Fin r) → C.point n (M , cs i) ≡ C.point n (xs i))

  finiteTaggedRepresentatives : (n r : ℕ) (xs : Fin r → C.Tagged n)
    → TaggedRepresentation n r xs
  finiteTaggedRepresentatives n r xs =
    let b = finiteBound r xs
        cs : Fin r → Cell (A (fst b)) n
        cs i = advanceCell (snd b i) n (snd (xs i))
    in fst b , cs , λ i → sym (point-advance (snd b i) n (snd (xs i)))

  Representation : (n r : ℕ) → (Fin r → C.Points n) → Type ℓ
  Representation n r xs = Σ[ M ∈ ℕ ] Σ[ cs ∈ (Fin r → Cell (A M) n) ]
    ((i : Fin r) → C.point n (M , cs i) ≡ xs i)

  pointRepresentative : (n : ℕ) (x : C.Points n)
    → ∥ Σ[ k ∈ ℕ ] Σ[ c ∈ Cell (A k) n ] C.point n (k , c) ≡ x ∥₁
  pointRepresentative n = SQ.elimProp (λ _ → squash₁)
    (λ { (k , c) → ∣ k , c , refl ∣₁ })

  -- 输入只给商中的点时，只能要求“截断存在一个共同阶段”。
  -- 对有限 Fin r 逐项消去截断即可；没有使用无限/可数选择。
  finiteRepresentatives : (n r : ℕ) (xs : Fin r → C.Points n)
    → ∥ Representation n r xs ∥₁
  finiteRepresentatives n zero xs = ∣ zero , (λ ()) , (λ ()) ∣₁
  finiteRepresentatives n (suc r) xs =
    PT.rec squash₁ (λ { (k , c , ec) →
      PT.rec squash₁ (λ { (l , ds , ed) →
        let M = max k l
            cs : Fin (suc r) → Cell (A M) n
            cs = λ where
              fzero → advanceCell (left-≤-max {m = k} {n = l}) n c
              (fsuc i) → advanceCell (right-≤-max {n = l} {m = k}) n (ds i)
            e : (i : Fin (suc r)) → C.point n (M , cs i) ≡ xs i
            e = λ where
              fzero → sym (point-advance (left-≤-max {m = k} {n = l}) n c) ∙ ec
              (fsuc i) → sym (point-advance (right-≤-max {n = l} {m = k}) n (ds i)) ∙ ed i
        in ∣ M , cs , e ∣₁ })
        (finiteRepresentatives n r (λ i → xs (fsuc i))) })
      (pointRepresentative n (xs fzero))
