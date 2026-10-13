{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayUnit where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; _+_)
open import Cubical.Data.Unit using (tt)
open import Cubical.Categories.Category.Base using (Category; CatIso; catiso)
open import DHH.Graph
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCategory.Coordinates using (appendHomExt)
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor

private variable ℓ : Level

DayUnit : CubicalSet ℓ-zero
DayUnit = RepresentableCube zero

-- 空的左坐标块不改变顶点函数；generated 字段是命题，由外延性处理。
tensor-left-unit : {m n : ℕ} (f : CubicalMap m n) → cubeId zero ⊗c f ≡ f
tensor-left-unit f = cubeMapExt (homExt (λ _ → refl))

private
  left-unit-chart : {p p' q q' : ℕ}
    (f : CubicalMap p p') (g : CubicalMap q q') (v : CubicalMap p' zero)
    → (((f ⋆c v) ⊗c cubeId q) ⋆c g) ≡ ((f ⊗c g) ⋆c (v ⊗c cubeId q'))
  left-unit-chart {p} {p'} {q} {q'} f g v = cubeMapExt
    (appendHomExt {m = p} {n = q} {k = q'} λ x y →
      cong (onVertices (underlying g)) (tensor-on-append (f ⋆c v) (cubeId q) x y)
      ∙ sym (cong (onVertices (underlying (v ⊗c cubeId q')))
          (tensor-on-append f g x y)
        ∙ tensor-on-append v (cubeId q')
          (onVertices (underlying f) x) (onVertices (underlying g) y)))

module _ {ℓ : Level} (A : CubicalSet ℓ) where
  -- 单位的 p-cell 是 p→0 的真实立方态射。把它和右块恒等态射
  -- 拼接，便能直接重索引 A 的 cell；没有挑选 coend 代表元。
  leftUnitPairing : DayPairing DayUnit A A
  pairCells leftUnitPairing p q v a = reindex A (v ⊗c cubeId q) a
  pair-natural leftUnitPairing {p} {p'} {q} {q'} f g v a =
    sym (reindex-compose A ((f ⋆c v) ⊗c cubeId q) g a)
    ∙ cong (λ u → reindex A u a) (left-unit-chart f g v)
    ∙ reindex-compose A (f ⊗c g) (v ⊗c cubeId q') a

  dayLeftUnit : CubicalNatural (DayTensor DayUnit A) A
  dayLeftUnit = factorDay {A = DayUnit} {B = A} {C = A} leftUnitPairing

  dayLeftUnit-β : (p q : ℕ) (v : CubicalMap p zero) (a : Cell A q)
    → mapCells dayLeftUnit (p + q) (dayPair {A = DayUnit} {B = A} p q v a)
      ≡ reindex A (v ⊗c cubeId q) a
  dayLeftUnit-β = factorDay-β {A = DayUnit} {B = A} {C = A} leftUnitPairing

  -- 逆映射加入零维恒等参数。所有次数都由同一个有限配对程序处理。
  dayLeftUnitInv : CubicalNatural A (DayTensor DayUnit A)
  mapCells dayLeftUnitInv n a = dayPair {A = DayUnit} {B = A} zero n (cubeId zero) a
  natural dayLeftUnitInv {m} {n} f a =
    cong (λ v → dayPair {A = DayUnit} {B = A} zero m v (reindex A f a))
      (sym (Category.⋆IdL CubeCategory (cubeId zero)))
    ∙ pair-natural (dayPairing DayUnit A) (cubeId zero) f (cubeId zero) a
    ∙ cong (λ u → reindex (DayTensor DayUnit A) u
        (dayPair {A = DayUnit} {B = A} zero n (cubeId zero) a)) (tensor-left-unit f)

  dayLeftUnit-section : dayLeftUnitInv ⋆n dayLeftUnit ≡ cubicalId A
  dayLeftUnit-section = cubicalNaturalExt λ n a →
    dayLeftUnit-β zero n (cubeId zero) a
    ∙ cong (λ u → reindex A u a) (tensor-id zero n)
    ∙ reindex-id A a

  dayLeftUnit-retract : dayLeftUnit ⋆n dayLeftUnitInv ≡ cubicalId (DayTensor DayUnit A)
  dayLeftUnit-retract =
    factorDay-unique {A = DayUnit} {B = A} {C = DayTensor DayUnit A}
      (dayPairing DayUnit A) (dayLeftUnit ⋆n dayLeftUnitInv)
      (λ p q v a →
        cong (mapCells dayLeftUnitInv (p + q)) (dayLeftUnit-β p q v a)
        ∙ natural dayLeftUnitInv (v ⊗c cubeId q) a
        ∙ sym (pair-natural (dayPairing DayUnit A) v (cubeId q) (cubeId zero) a)
        ∙ cong₂ (dayPair {A = DayUnit} {B = A} p q)
          (Category.⋆IdR CubeCategory v) (reindex-id A a))
    ∙ sym (factorDay-unique {A = DayUnit} {B = A} {C = DayTensor DayUnit A}
      (dayPairing DayUnit A) (cubicalId (DayTensor DayUnit A)) (λ _ _ _ _ → refl))

  dayLeftUnitIso : CatIso (CubicalSetCategory ℓ) (DayTensor DayUnit A) A
  dayLeftUnitIso = catiso dayLeftUnit dayLeftUnitInv dayLeftUnit-section dayLeftUnit-retract

  -- 右单位使用真实立方态射 n+0→n；这一步没有把非定义性的
  -- 自然数右单位等式当作 refl，也没有留下未声明的类型转换。
  rightUnitPairing : DayPairing A DayUnit A
  pairCells rightUnitPairing p q a v = reindex A ((cubeId p ⊗c v) ⋆c cubeRightUnit p) a
  pair-natural rightUnitPairing {p} {p'} {q} {q'} f g a v =
    sym (reindex-compose A ((cubeId p ⊗c (g ⋆c v)) ⋆c cubeRightUnit p) f a)
    ∙ cong (λ u → reindex A u a) (right-unit-chart f g v)
    ∙ reindex-compose A (f ⊗c g) ((cubeId p' ⊗c v) ⋆c cubeRightUnit p') a

  dayRightUnit : CubicalNatural (DayTensor A DayUnit) A
  dayRightUnit = factorDay {A = A} {B = DayUnit} {C = A} rightUnitPairing

  dayRightUnit-β : (p q : ℕ) (a : Cell A p) (v : CubicalMap q zero)
    → mapCells dayRightUnit (p + q) (dayPair {A = A} {B = DayUnit} p q a v)
      ≡ reindex A ((cubeId p ⊗c v) ⋆c cubeRightUnit p) a
  dayRightUnit-β = factorDay-β {A = A} {B = DayUnit} {C = A} rightUnitPairing

  dayRightUnitInv : CubicalNatural A (DayTensor A DayUnit)
  mapCells dayRightUnitInv n a = reindex (DayTensor A DayUnit) (cubeRightUnitInv n)
    (dayPair {A = A} {B = DayUnit} n zero a (cubeId zero))
  natural dayRightUnitInv {m} {n} f a =
    cong (reindex (DayTensor A DayUnit) (cubeRightUnitInv m))
      (cong (λ v → dayPair {A = A} {B = DayUnit} m zero (reindex A f a) v)
        (sym (Category.⋆IdL CubeCategory (cubeId zero)))
      ∙ pair-natural (dayPairing A DayUnit) f (cubeId zero) a (cubeId zero))
    ∙ sym (reindex-compose (DayTensor A DayUnit) (cubeRightUnitInv m) (f ⊗c cubeId zero)
      (dayPair {A = A} {B = DayUnit} n zero a (cubeId zero)))
    ∙ cong (λ u → reindex (DayTensor A DayUnit) u
      (dayPair {A = A} {B = DayUnit} n zero a (cubeId zero))) (cubeRightUnitInv-natural f)
    ∙ reindex-compose (DayTensor A DayUnit) f (cubeRightUnitInv n)
      (dayPair {A = A} {B = DayUnit} n zero a (cubeId zero))

  private
    rightUnit-unit-pair : (n : ℕ) (a : Cell A n)
      → mapCells dayRightUnit (n + zero) (dayPair {A = A} {B = DayUnit} n zero a (cubeId zero))
        ≡ reindex A (cubeRightUnit n) a
    rightUnit-unit-pair n a = dayRightUnit-β n zero a (cubeId zero)
      ∙ cong (λ u → reindex A u a)
        (cong (_⋆c cubeRightUnit n) (tensor-id n zero)
        ∙ Category.⋆IdL CubeCategory (cubeRightUnit n))

  dayRightUnit-section : dayRightUnitInv ⋆n dayRightUnit ≡ cubicalId A
  dayRightUnit-section = cubicalNaturalExt λ n a →
    natural dayRightUnit (cubeRightUnitInv n)
      (dayPair {A = A} {B = DayUnit} n zero a (cubeId zero))
    ∙ cong (reindex A (cubeRightUnitInv n)) (rightUnit-unit-pair n a)
    ∙ sym (reindex-compose A (cubeRightUnitInv n) (cubeRightUnit n) a)
    ∙ cong (λ u → reindex A u a) (cubeRightUnit-section n)
    ∙ reindex-id A a

  dayRightUnit-retract : dayRightUnit ⋆n dayRightUnitInv ≡ cubicalId (DayTensor A DayUnit)
  dayRightUnit-retract =
    factorDay-unique {A = A} {B = DayUnit} {C = DayTensor A DayUnit}
      (dayPairing A DayUnit) (dayRightUnit ⋆n dayRightUnitInv)
      (λ p q a v →
        cong (mapCells dayRightUnitInv (p + q)) (dayRightUnit-β p q a v)
        ∙ natural dayRightUnitInv ((cubeId p ⊗c v) ⋆c cubeRightUnit p) a
        ∙ sym (reindex-compose (DayTensor A DayUnit)
          ((cubeId p ⊗c v) ⋆c cubeRightUnit p) (cubeRightUnitInv p)
          (dayPair {A = A} {B = DayUnit} p zero a (cubeId zero)))
        ∙ cong (λ u → reindex (DayTensor A DayUnit) u
            (dayPair {A = A} {B = DayUnit} p zero a (cubeId zero)))
          (Category.⋆Assoc CubeCategory (cubeId p ⊗c v) (cubeRightUnit p) (cubeRightUnitInv p)
          ∙ cong ((cubeId p ⊗c v) ⋆c_) (cubeRightUnit-retract p)
          ∙ Category.⋆IdR CubeCategory (cubeId p ⊗c v))
        ∙ sym (pair-natural (dayPairing A DayUnit) (cubeId p) v a (cubeId zero))
        ∙ cong₂ (dayPair {A = A} {B = DayUnit} p q)
          (reindex-id A a) (Category.⋆IdR CubeCategory v))
    ∙ sym (factorDay-unique {A = A} {B = DayUnit} {C = DayTensor A DayUnit}
      (dayPairing A DayUnit) (cubicalId (DayTensor A DayUnit)) (λ _ _ _ _ → refl))

  dayRightUnitIso : CatIso (CubicalSetCategory ℓ) (DayTensor A DayUnit) A
  dayRightUnitIso = catiso dayRightUnit dayRightUnitInv dayRightUnit-section dayRightUnit-retract
