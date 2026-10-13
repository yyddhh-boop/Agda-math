{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayUnitLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; _+_)
open import Cubical.Data.Sigma
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.Cubical.DayAssociatorHelpers
open import DHH.Cubical.DayTriple
open import DHH.Cubical.DayAssociator
open import DHH.Cubical.DayUnit
open import DHH.Cubical.DayCoherence using (dayTriangle-chart)

-- 显式 Lift 提升单位，不使用 resizing 或 universe cumulativity。
DayUnitAt : (ℓ : Level) → CubicalSet ℓ
cells (DayUnitAt ℓ) n = Lift {j = ℓ} (Cell DayUnit n) , isOfHLevelLift 2 (snd (cells DayUnit n))
reindex (DayUnitAt ℓ) f v = lift (reindex DayUnit f (lower v))
reindex-id (DayUnitAt ℓ) v = cong lift (reindex-id DayUnit (lower v))
reindex-compose (DayUnitAt ℓ) f g v = cong lift (reindex-compose DayUnit f g (lower v))

lowerDayUnit : (ℓ : Level) → CubicalNatural (DayUnitAt ℓ) DayUnit
mapCells (lowerDayUnit ℓ) n v = lower v
natural (lowerDayUnit ℓ) f v = refl

raiseDayUnit : (ℓ : Level) → CubicalNatural DayUnit (DayUnitAt ℓ)
mapCells (raiseDayUnit ℓ) n v = lift v
natural (raiseDayUnit ℓ) f v = refl

raise-lower-DayUnit : (ℓ : Level) → raiseDayUnit ℓ ⋆n lowerDayUnit ℓ ≡ cubicalId DayUnit
raise-lower-DayUnit ℓ = cubicalNaturalExt λ n v → refl

lower-raise-DayUnit : (ℓ : Level) → lowerDayUnit ℓ ⋆n raiseDayUnit ℓ ≡ cubicalId (DayUnitAt ℓ)
lower-raise-DayUnit ℓ = cubicalNaturalExt λ n v → refl

module _ {ℓ : Level} (A : CubicalSet ℓ) where
  private
    lowerLeft : CubicalNatural (DayTensor (DayUnitAt ℓ) A) (DayTensor DayUnit A)
    lowerLeft = dayMap (lowerDayUnit ℓ) (cubicalId A)
    raiseLeft : CubicalNatural (DayTensor DayUnit A) (DayTensor (DayUnitAt ℓ) A)
    raiseLeft = dayMap (raiseDayUnit ℓ) (cubicalId A)
    lowerRight : CubicalNatural (DayTensor A (DayUnitAt ℓ)) (DayTensor A DayUnit)
    lowerRight = dayMap (cubicalId A) (lowerDayUnit ℓ)
    raiseRight : CubicalNatural (DayTensor A DayUnit) (DayTensor A (DayUnitAt ℓ))
    raiseRight = dayMap (cubicalId A) (raiseDayUnit ℓ)

    id-compose : cubicalId A ⋆n cubicalId A ≡ cubicalId A
    id-compose = cubicalNaturalExt λ n a → refl

    raise-lower-left : raiseLeft ⋆n lowerLeft ≡ cubicalId (DayTensor DayUnit A)
    raise-lower-left = sym (dayMap-compose (raiseDayUnit ℓ) (lowerDayUnit ℓ) (cubicalId A) (cubicalId A))
      ∙ cong₂ dayMap (raise-lower-DayUnit ℓ) id-compose ∙ dayMap-id DayUnit A

    lower-raise-left : lowerLeft ⋆n raiseLeft ≡ cubicalId (DayTensor (DayUnitAt ℓ) A)
    lower-raise-left = sym (dayMap-compose (lowerDayUnit ℓ) (raiseDayUnit ℓ) (cubicalId A) (cubicalId A))
      ∙ cong₂ dayMap (lower-raise-DayUnit ℓ) id-compose ∙ dayMap-id (DayUnitAt ℓ) A

    raise-lower-right : raiseRight ⋆n lowerRight ≡ cubicalId (DayTensor A DayUnit)
    raise-lower-right = sym (dayMap-compose (cubicalId A) (cubicalId A) (raiseDayUnit ℓ) (lowerDayUnit ℓ))
      ∙ cong₂ dayMap id-compose (raise-lower-DayUnit ℓ) ∙ dayMap-id A DayUnit

    lower-raise-right : lowerRight ⋆n raiseRight ≡ cubicalId (DayTensor A (DayUnitAt ℓ))
    lower-raise-right = sym (dayMap-compose (cubicalId A) (cubicalId A) (lowerDayUnit ℓ) (raiseDayUnit ℓ))
      ∙ cong₂ dayMap id-compose (lower-raise-DayUnit ℓ) ∙ dayMap-id A (DayUnitAt ℓ)

  dayLeftUnitAt : CubicalNatural (DayTensor (DayUnitAt ℓ) A) A
  dayLeftUnitAt = lowerLeft ⋆n dayLeftUnit A

  dayLeftUnitAtInv : CubicalNatural A (DayTensor (DayUnitAt ℓ) A)
  dayLeftUnitAtInv = dayLeftUnitInv A ⋆n raiseLeft

  dayLeftUnitAt-β : (p q : ℕ) (v : Cell (DayUnitAt ℓ) p) (a : Cell A q)
    → mapCells dayLeftUnitAt (p + q) (dayPair {A = DayUnitAt ℓ} {B = A} p q v a)
      ≡ reindex A (lower v ⊗c cubeId q) a
  dayLeftUnitAt-β p q v a =
    cong (mapCells (dayLeftUnit A) (p + q)) (dayMap-β (lowerDayUnit ℓ) (cubicalId A) p q v a)
    ∙ dayLeftUnit-β A p q (lower v) a

  dayLeftUnitAt-section : dayLeftUnitAtInv ⋆n dayLeftUnitAt ≡ cubicalId A
  dayLeftUnitAt-section = cubicalNaturalExt λ n a →
    cong (mapCells (dayLeftUnit A) n)
      (cong (λ F → mapCells F n (mapCells (dayLeftUnitInv A) n a)) raise-lower-left)
    ∙ cong (λ F → mapCells F n a) (dayLeftUnit-section A)

  dayLeftUnitAt-retract : dayLeftUnitAt ⋆n dayLeftUnitAtInv ≡ cubicalId (DayTensor (DayUnitAt ℓ) A)
  dayLeftUnitAt-retract = cubicalNaturalExt λ n x →
    cong (mapCells raiseLeft n) (cong (λ F → mapCells F n (mapCells lowerLeft n x)) (dayLeftUnit-retract A))
    ∙ cong (λ F → mapCells F n x) lower-raise-left

  dayRightUnitAt : CubicalNatural (DayTensor A (DayUnitAt ℓ)) A
  dayRightUnitAt = lowerRight ⋆n dayRightUnit A

  dayRightUnitAtInv : CubicalNatural A (DayTensor A (DayUnitAt ℓ))
  dayRightUnitAtInv = dayRightUnitInv A ⋆n raiseRight

  dayRightUnitAt-β : (p q : ℕ) (a : Cell A p) (v : Cell (DayUnitAt ℓ) q)
    → mapCells dayRightUnitAt (p + q) (dayPair {A = A} {B = DayUnitAt ℓ} p q a v)
      ≡ reindex A ((cubeId p ⊗c lower v) ⋆c cubeRightUnit p) a
  dayRightUnitAt-β p q a v =
    cong (mapCells (dayRightUnit A) (p + q)) (dayMap-β (cubicalId A) (lowerDayUnit ℓ) p q a v)
    ∙ dayRightUnit-β A p q a (lower v)

  dayRightUnitAt-section : dayRightUnitAtInv ⋆n dayRightUnitAt ≡ cubicalId A
  dayRightUnitAt-section = cubicalNaturalExt λ n a →
    cong (mapCells (dayRightUnit A) n)
      (cong (λ F → mapCells F n (mapCells (dayRightUnitInv A) n a)) raise-lower-right)
    ∙ cong (λ F → mapCells F n a) (dayRightUnit-section A)

  dayRightUnitAt-retract : dayRightUnitAt ⋆n dayRightUnitAtInv ≡ cubicalId (DayTensor A (DayUnitAt ℓ))
  dayRightUnitAt-retract = cubicalNaturalExt λ n x →
    cong (mapCells raiseRight n) (cong (λ F → mapCells F n (mapCells lowerRight n x)) (dayRightUnit-retract A))
    ∙ cong (λ F → mapCells F n x) lower-raise-right

module _ {ℓ : Level} {A B : CubicalSet ℓ} (F : CubicalNatural A B) where
  dayLeftUnitAt-natural : dayMap (cubicalId (DayUnitAt ℓ)) F ⋆n dayLeftUnitAt B ≡ dayLeftUnitAt A ⋆n F
  dayLeftUnitAt-natural = dayTensorExt _ _ λ p q v a →
    cong (mapCells (dayLeftUnitAt B) (p + q)) (dayMap-β (cubicalId (DayUnitAt ℓ)) F p q v a)
    ∙ dayLeftUnitAt-β B p q v (mapCells F q a)
    ∙ sym (natural F (lower v ⊗c cubeId q) a)
    ∙ sym (cong (mapCells F (p + q)) (dayLeftUnitAt-β A p q v a))

  dayRightUnitAt-natural : dayMap F (cubicalId (DayUnitAt ℓ)) ⋆n dayRightUnitAt B ≡ dayRightUnitAt A ⋆n F
  dayRightUnitAt-natural = dayTensorExt _ _ λ p q a v →
    cong (mapCells (dayRightUnitAt B) (p + q)) (dayMap-β F (cubicalId (DayUnitAt ℓ)) p q a v)
    ∙ dayRightUnitAt-β B p q (mapCells F p a) v
    ∙ sym (natural F ((cubeId p ⊗c lower v) ⋆c cubeRightUnit p) a)
    ∙ sym (cong (mapCells F (p + q)) (dayRightUnitAt-β A p q a v))

dayTriangleAt : {ℓ : Level} (A B : CubicalSet ℓ)
  → dayAssociatorInv A (DayUnitAt ℓ) B ⋆n dayMap (dayRightUnitAt A) (cubicalId B)
    ≡ dayMap (cubicalId A) (dayLeftUnitAt B)
dayTriangleAt {ℓ} A B = TripleExt.rightTripleExt A (DayUnitAt ℓ) B (DayTensor A B) _ _ λ p q r a v b →
  let T = DayTensor A B
      u = cubeAssociatorInv p q r
      w = (cubeId p ⊗c lower v) ⋆c cubeRightUnit p
      t = dayPair {A = A} {B = B} p r a b
      M = dayMap (dayRightUnitAt A) (cubicalId B)
  in cong (mapCells M (p + (q + r))) (dayAssociatorInv-β A (DayUnitAt ℓ) B p q r a v b)
    ∙ natural M u (leftTripleCell A (DayUnitAt ℓ) B p q r a v b)
    ∙ cong (reindex T u)
      (dayMap-β (dayRightUnitAt A) (cubicalId B) (p + q) r
        (dayPair {A = A} {B = DayUnitAt ℓ} p q a v) b
      ∙ cong (λ c → dayPair {A = A} {B = B} (p + q) r c b) (dayRightUnitAt-β A p q a v)
      ∙ dayPair-left {A = A} {B = B} w a b)
    ∙ sym (reindex-compose T u (w ⊗c cubeId r) t)
    ∙ cong (λ f → reindex T f t) (dayTriangle-chart p q r (lower v))
    ∙ sym (dayMap-β (cubicalId A) (dayLeftUnitAt B) p (q + r) a
        (dayPair {A = DayUnitAt ℓ} {B = B} q r v b)
      ∙ cong (dayPair {A = A} {B = B} p (q + r) a) (dayLeftUnitAt-β B q r v b)
      ∙ dayPair-right {A = A} {B = B} (lower v ⊗c cubeId r) a b)
