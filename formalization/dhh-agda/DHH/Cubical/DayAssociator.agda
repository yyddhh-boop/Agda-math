{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayAssociator where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import Cubical.Categories.Category.Base using (CatIso; catiso)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTriple

private variable ℓA ℓB ℓC : Level

module _ {ℓA ℓB ℓC : Level}
  (A : CubicalSet ℓA) (B : CubicalSet ℓB) (C : CubicalSet ℓC) where
  private
    L : CubicalSet (ℓ-max ℓA (ℓ-max ℓB ℓC))
    L = DayTensor (DayTensor A B) C
    R : CubicalSet (ℓ-max ℓA (ℓ-max ℓB ℓC))
    R = DayTensor A (DayTensor B C)

  leftTripleCell : (p q r : ℕ) → Cell A p → Cell B q → Cell C r → Cell L ((p + q) + r)
  leftTripleCell p q r a b c = dayPair {A = DayTensor A B} {B = C} (p + q) r
    (dayPair {A = A} {B = B} p q a b) c

  rightTripleCell : (p q r : ℕ) → Cell A p → Cell B q → Cell C r → Cell R (p + (q + r))
  rightTripleCell p q r a b c = dayPair {A = A} {B = DayTensor B C} p (q + r) a
    (dayPair {A = B} {B = C} q r b c)

  leftTripleCell-natural : {p p' q q' r r' : ℕ}
    (f : CubicalMap p p') (g : CubicalMap q q') (h : CubicalMap r r')
    (a : Cell A p') (b : Cell B q') (c : Cell C r')
    → leftTripleCell p q r (reindex A f a) (reindex B g b) (reindex C h c)
      ≡ reindex L ((f ⊗c g) ⊗c h) (leftTripleCell p' q' r' a b c)
  leftTripleCell-natural {p} {p'} {q} {q'} {r} {r'} f g h a b c =
    cong (λ ab → dayPair {A = DayTensor A B} {B = C} (p + q) r ab (reindex C h c))
      (pair-natural (dayPairing A B) f g a b)
    ∙ pair-natural (dayPairing (DayTensor A B) C) (f ⊗c g) h (dayPair {A = A} {B = B} p' q' a b) c

  rightTripleCell-natural : {p p' q q' r r' : ℕ}
    (f : CubicalMap p p') (g : CubicalMap q q') (h : CubicalMap r r')
    (a : Cell A p') (b : Cell B q') (c : Cell C r')
    → rightTripleCell p q r (reindex A f a) (reindex B g b) (reindex C h c)
      ≡ reindex R (f ⊗c (g ⊗c h)) (rightTripleCell p' q' r' a b c)
  rightTripleCell-natural {p} {p'} {q} {q'} {r} {r'} f g h a b c =
    cong (dayPair {A = A} {B = DayTensor B C} p (q + r) (reindex A f a))
      (pair-natural (dayPairing B C) g h b c)
    ∙ pair-natural (dayPairing A (DayTensor B C)) f (g ⊗c h) a (dayPair {A = B} {B = C} q' r' b c)

  -- 三块生成元只改变括号；cubeAssociator 把次数 ((p+q)+r)
  -- 对齐到 p+(q+r)。两个商层的全部关系由 TripleFactor 降商处理。
  associatorPairing : TriplePairing A B C R
  triple associatorPairing p q r a b c =
    reindex R (cubeAssociator p q r) (rightTripleCell p q r a b c)
  triple-natural associatorPairing {p} {p'} {q} {q'} {r} {r'} f g h a b c =
    cong (reindex R (cubeAssociator p q r)) (rightTripleCell-natural f g h a b c)
    ∙ sym (reindex-compose R (cubeAssociator p q r) (f ⊗c (g ⊗c h)) (rightTripleCell p' q' r' a b c))
    ∙ cong (λ u → reindex R u (rightTripleCell p' q' r' a b c)) (sym (cubeAssociator-natural f g h))
    ∙ reindex-compose R ((f ⊗c g) ⊗c h) (cubeAssociator p' q' r') (rightTripleCell p' q' r' a b c)

  inverseAssociatorPairing : RightTriplePairing A B C L
  rightTriple inverseAssociatorPairing p q r a b c =
    reindex L (cubeAssociatorInv p q r) (leftTripleCell p q r a b c)
  rightTriple-natural inverseAssociatorPairing {p} {p'} {q} {q'} {r} {r'} f g h a b c =
    cong (reindex L (cubeAssociatorInv p q r)) (leftTripleCell-natural f g h a b c)
    ∙ sym (reindex-compose L (cubeAssociatorInv p q r) ((f ⊗c g) ⊗c h) (leftTripleCell p' q' r' a b c))
    ∙ cong (λ u → reindex L u (leftTripleCell p' q' r' a b c)) (sym (cubeAssociatorInv-natural f g h))
    ∙ reindex-compose L (f ⊗c (g ⊗c h)) (cubeAssociatorInv p' q' r') (leftTripleCell p' q' r' a b c)

  dayAssociator : CubicalNatural L R
  dayAssociator = LeftFactor.factorLeftTriple A B C R associatorPairing

  dayAssociatorInv : CubicalNatural R L
  dayAssociatorInv = RightFactor.factorRightTriple A B C L inverseAssociatorPairing

  dayAssociator-β : (p q r : ℕ) (a : Cell A p) (b : Cell B q) (c : Cell C r)
    → mapCells dayAssociator ((p + q) + r) (leftTripleCell p q r a b c)
      ≡ reindex R (cubeAssociator p q r) (rightTripleCell p q r a b c)
  dayAssociator-β = LeftFactor.factorLeftTriple-β A B C R associatorPairing

  dayAssociatorInv-β : (p q r : ℕ) (a : Cell A p) (b : Cell B q) (c : Cell C r)
    → mapCells dayAssociatorInv (p + (q + r)) (rightTripleCell p q r a b c)
      ≡ reindex L (cubeAssociatorInv p q r) (leftTripleCell p q r a b c)
  dayAssociatorInv-β = RightFactor.factorRightTriple-β A B C L inverseAssociatorPairing

  -- 等式在两层商的三块生成元上验证，然后由三变量外延性推出
  -- 全部自然变换相等。没有把集合商的代表选择当作算法步骤。
  dayAssociator-section : dayAssociatorInv ⋆n dayAssociator ≡ cubicalId R
  dayAssociator-section = TripleExt.rightTripleExt A B C R
    (dayAssociatorInv ⋆n dayAssociator) (cubicalId R) λ p q r a b c →
      cong (mapCells dayAssociator (p + (q + r))) (dayAssociatorInv-β p q r a b c)
      ∙ natural dayAssociator (cubeAssociatorInv p q r) (leftTripleCell p q r a b c)
      ∙ cong (reindex R (cubeAssociatorInv p q r)) (dayAssociator-β p q r a b c)
      ∙ sym (reindex-compose R (cubeAssociatorInv p q r) (cubeAssociator p q r) (rightTripleCell p q r a b c))
      ∙ cong (λ u → reindex R u (rightTripleCell p q r a b c)) (cubeAssociator-section p q r)
      ∙ reindex-id R (rightTripleCell p q r a b c)

  dayAssociator-retract : dayAssociator ⋆n dayAssociatorInv ≡ cubicalId L
  dayAssociator-retract = TripleExt.leftTripleExt A B C L
    (dayAssociator ⋆n dayAssociatorInv) (cubicalId L) λ p q r a b c →
      cong (mapCells dayAssociatorInv ((p + q) + r)) (dayAssociator-β p q r a b c)
      ∙ natural dayAssociatorInv (cubeAssociator p q r) (rightTripleCell p q r a b c)
      ∙ cong (reindex L (cubeAssociator p q r)) (dayAssociatorInv-β p q r a b c)
      ∙ sym (reindex-compose L (cubeAssociator p q r) (cubeAssociatorInv p q r) (leftTripleCell p q r a b c))
      ∙ cong (λ u → reindex L u (leftTripleCell p q r a b c)) (cubeAssociator-retract p q r)
      ∙ reindex-id L (leftTripleCell p q r a b c)

  dayAssociatorIso : CatIso (CubicalSetCategory (ℓ-max ℓA (ℓ-max ℓB ℓC))) L R
  dayAssociatorIso = catiso dayAssociator dayAssociatorInv dayAssociator-section dayAssociator-retract
