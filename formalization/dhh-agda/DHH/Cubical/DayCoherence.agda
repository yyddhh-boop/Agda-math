{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayCoherence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; _+_)
open import DHH.Graph
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCategory.Coordinates using (appendPoint)
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.Cubical.DayAssociatorHelpers
open import DHH.Cubical.DayTriple
open import DHH.Cubical.DayAssociator
open import DHH.Cubical.DayUnit

private variable ℓA ℓA' ℓB ℓB' ℓC ℓC' : Level

-- 参数自然性比较实际的自然变换；三块生成元外延性覆盖全部次数。
dayMap-leftTriple-β : {A : CubicalSet ℓA} {A' : CubicalSet ℓA'}
  {B : CubicalSet ℓB} {B' : CubicalSet ℓB'} {C : CubicalSet ℓC} {C' : CubicalSet ℓC'}
  (F : CubicalNatural A A') (G : CubicalNatural B B') (H : CubicalNatural C C')
  (p q r : ℕ) (a : Cell A p) (b : Cell B q) (c : Cell C r)
  → mapCells (dayMap (dayMap F G) H) ((p + q) + r) (leftTripleCell A B C p q r a b c)
    ≡ leftTripleCell A' B' C' p q r (mapCells F p a) (mapCells G q b) (mapCells H r c)
dayMap-leftTriple-β {A = A} {A'} {B} {B'} {C} {C'} F G H p q r a b c =
  dayMap-β (dayMap F G) H (p + q) r (dayPair {A = A} {B = B} p q a b) c
  ∙ cong (λ ab → dayPair {A = DayTensor A' B'} {B = C'} (p + q) r ab (mapCells H r c))
    (dayMap-β F G p q a b)

dayMap-rightTriple-β : {A : CubicalSet ℓA} {A' : CubicalSet ℓA'}
  {B : CubicalSet ℓB} {B' : CubicalSet ℓB'} {C : CubicalSet ℓC} {C' : CubicalSet ℓC'}
  (F : CubicalNatural A A') (G : CubicalNatural B B') (H : CubicalNatural C C')
  (p q r : ℕ) (a : Cell A p) (b : Cell B q) (c : Cell C r)
  → mapCells (dayMap F (dayMap G H)) (p + (q + r)) (rightTripleCell A B C p q r a b c)
    ≡ rightTripleCell A' B' C' p q r (mapCells F p a) (mapCells G q b) (mapCells H r c)
dayMap-rightTriple-β {A = A} {A'} {B} {B'} {C} {C'} F G H p q r a b c =
  dayMap-β F (dayMap G H) p (q + r) a (dayPair {A = B} {B = C} q r b c)
  ∙ cong (dayPair {A = A'} {B = DayTensor B' C'} p (q + r) (mapCells F p a))
    (dayMap-β G H q r b c)

dayAssociator-natural : {A : CubicalSet ℓA} {A' : CubicalSet ℓA'}
  {B : CubicalSet ℓB} {B' : CubicalSet ℓB'} {C : CubicalSet ℓC} {C' : CubicalSet ℓC'}
  (F : CubicalNatural A A') (G : CubicalNatural B B') (H : CubicalNatural C C')
  → dayMap (dayMap F G) H ⋆n dayAssociator A' B' C'
    ≡ dayAssociator A B C ⋆n dayMap F (dayMap G H)
dayAssociator-natural {A = A} {A'} {B} {B'} {C} {C'} F G H =
  TripleExt.leftTripleExt A B C (DayTensor A' (DayTensor B' C')) _ _ λ p q r a b c →
    cong (mapCells (dayAssociator A' B' C') ((p + q) + r))
      (dayMap-leftTriple-β F G H p q r a b c)
    ∙ dayAssociator-β A' B' C' p q r (mapCells F p a) (mapCells G q b) (mapCells H r c)
    ∙ sym (cong (mapCells (dayMap F (dayMap G H)) ((p + q) + r))
        (dayAssociator-β A B C p q r a b c)
      ∙ natural (dayMap F (dayMap G H)) (cubeAssociator p q r) (rightTripleCell A B C p q r a b c)
      ∙ cong (reindex (DayTensor A' (DayTensor B' C')) (cubeAssociator p q r))
        (dayMap-rightTriple-β F G H p q r a b c))

dayAssociatorInv-natural : {A : CubicalSet ℓA} {A' : CubicalSet ℓA'}
  {B : CubicalSet ℓB} {B' : CubicalSet ℓB'} {C : CubicalSet ℓC} {C' : CubicalSet ℓC'}
  (F : CubicalNatural A A') (G : CubicalNatural B B') (H : CubicalNatural C C')
  → dayMap F (dayMap G H) ⋆n dayAssociatorInv A' B' C'
    ≡ dayAssociatorInv A B C ⋆n dayMap (dayMap F G) H
dayAssociatorInv-natural {A = A} {A'} {B} {B'} {C} {C'} F G H =
  TripleExt.rightTripleExt A B C (DayTensor (DayTensor A' B') C') _ _ λ p q r a b c →
    cong (mapCells (dayAssociatorInv A' B' C') (p + (q + r)))
      (dayMap-rightTriple-β F G H p q r a b c)
    ∙ dayAssociatorInv-β A' B' C' p q r (mapCells F p a) (mapCells G q b) (mapCells H r c)
    ∙ sym (cong (mapCells (dayMap (dayMap F G) H) (p + (q + r)))
        (dayAssociatorInv-β A B C p q r a b c)
      ∙ natural (dayMap (dayMap F G) H) (cubeAssociatorInv p q r) (leftTripleCell A B C p q r a b c)
      ∙ cong (reindex (DayTensor (DayTensor A' B') C') (cubeAssociatorInv p q r))
        (dayMap-leftTriple-β F G H p q r a b c))

dayLeftUnit-natural : {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  (F : CubicalNatural A B)
  → dayMap (cubicalId DayUnit) F ⋆n dayLeftUnit B ≡ dayLeftUnit A ⋆n F
dayLeftUnit-natural {A = A} {B} F = dayTensorExt _ _ λ p q v a →
  cong (mapCells (dayLeftUnit B) (p + q)) (dayMap-β (cubicalId DayUnit) F p q v a)
  ∙ dayLeftUnit-β B p q v (mapCells F q a)
  ∙ sym (natural F (v ⊗c cubeId q) a)
  ∙ sym (cong (mapCells F (p + q)) (dayLeftUnit-β A p q v a))

dayRightUnit-natural : {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  (F : CubicalNatural A B)
  → dayMap F (cubicalId DayUnit) ⋆n dayRightUnit B ≡ dayRightUnit A ⋆n F
dayRightUnit-natural {A = A} {B} F = dayTensorExt _ _ λ p q a v →
  cong (mapCells (dayRightUnit B) (p + q)) (dayMap-β F (cubicalId DayUnit) p q a v)
  ∙ dayRightUnit-β B p q (mapCells F p a) v
  ∙ sym (natural F ((cubeId p ⊗c v) ⋆c cubeRightUnit p) a)
  ∙ sym (cong (mapCells F (p + q)) (dayRightUnit-β A p q a v))

-- 单位参数可在任意次数 q 出现。图侧逐坐标公式收起这个块，
-- 而不是只核对 q=0 或有限多个顶点赋值。
dayTriangle-chart : (p q r : ℕ) (v : CubicalMap q zero)
  → cubeAssociatorInv p q r ⋆c (((cubeId p ⊗c v) ⋆c cubeRightUnit p) ⊗c cubeId r)
    ≡ cubeId p ⊗c (v ⊗c cubeId r)
dayTriangle-chart p q r v = cubeMapExt
  (rightTripleHomExt {p = p} {q = q} {r = r} {k = p + r}
    {f = underlying (cubeAssociatorInv p q r ⋆c (((cubeId p ⊗c v) ⋆c cubeRightUnit p) ⊗c cubeId r))}
    {g = underlying (cubeId p ⊗c (v ⊗c cubeId r))} λ x y z →
    cong (onVertices (underlying (((cubeId p ⊗c v) ⋆c cubeRightUnit p) ⊗c cubeId r)))
      (cubeAssociatorInv-on-append p q r x y z)
    ∙ tensor-on-append ((cubeId p ⊗c v) ⋆c cubeRightUnit p) (cubeId r)
      (appendPoint p q x y) z
    ∙ cong (λ t → appendPoint p r t z) (rightUnit-collapse p q v x y)
    ∙ sym (tensor-on-append (cubeId p) (v ⊗c cubeId r) x (appendPoint q r y z)
      ∙ cong (appendPoint p r x) (tensor-on-append v (cubeId r) y z)))

dayTriangle : (A : CubicalSet ℓA) (B : CubicalSet ℓB)
  → dayAssociatorInv A DayUnit B ⋆n dayMap (dayRightUnit A) (cubicalId B)
    ≡ dayMap (cubicalId A) (dayLeftUnit B)
dayTriangle A B = TripleExt.rightTripleExt A DayUnit B (DayTensor A B) _ _ λ p q r a v b →
  let T = DayTensor A B
      u = cubeAssociatorInv p q r
      w = (cubeId p ⊗c v) ⋆c cubeRightUnit p
      t = dayPair {A = A} {B = B} p r a b
      M = dayMap (dayRightUnit A) (cubicalId B)
  in cong (mapCells M (p + (q + r))) (dayAssociatorInv-β A DayUnit B p q r a v b)
    ∙ natural M u (leftTripleCell A DayUnit B p q r a v b)
    ∙ cong (reindex T u)
      (dayMap-β (dayRightUnit A) (cubicalId B) (p + q) r
        (dayPair {A = A} {B = DayUnit} p q a v) b
      ∙ cong (λ c → dayPair {A = A} {B = B} (p + q) r c b) (dayRightUnit-β A p q a v)
      ∙ dayPair-left {A = A} {B = B} w a b)
    ∙ sym (reindex-compose T u (w ⊗c cubeId r) t)
    ∙ cong (λ f → reindex T f t) (dayTriangle-chart p q r v)
    ∙ sym (dayMap-β (cubicalId A) (dayLeftUnit B) p (q + r) a
        (dayPair {A = DayUnit} {B = B} q r v b)
      ∙ cong (dayPair {A = A} {B = B} p (q + r) a) (dayLeftUnit-β B q r v b)
      ∙ dayPair-right {A = A} {B = B} (v ⊗c cubeId r) a b)
