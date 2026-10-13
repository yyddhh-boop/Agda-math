{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayTensorFunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import DHH.CubicalNerve
open import DHH.Cubical.DayTensor

private variable ℓA ℓA' ℓA'' ℓB ℓB' ℓB'' ℓC ℓD : Level

-- 两个预层自然变换先作用于独立的两块 cell，然后送入普遍配对。
-- 商的普遍性质负责降商；恒等律和复合律由配对生成元上的公式推出。
dayMapPairing : {A : CubicalSet ℓA} {A' : CubicalSet ℓA'}
  {B : CubicalSet ℓB} {B' : CubicalSet ℓB'}
  → CubicalNatural A A' → CubicalNatural B B' → DayPairing A B (DayTensor A' B')
pairCells (dayMapPairing {A' = A'} {B' = B'} F G) p q a b =
  dayPair {A = A'} {B = B'} p q (mapCells F p a) (mapCells G q b)
pair-natural (dayMapPairing {A' = A'} {B' = B'} F G) {p} {p'} {q} {q'} f g a b =
  cong₂ (dayPair {A = A'} {B = B'} p q) (natural F f a) (natural G g b)
  ∙ pair-natural (dayPairing A' B') f g (mapCells F p' a) (mapCells G q' b)

dayMap : {A : CubicalSet ℓA} {A' : CubicalSet ℓA'} {B : CubicalSet ℓB} {B' : CubicalSet ℓB'}
  → CubicalNatural A A' → CubicalNatural B B' → CubicalNatural (DayTensor A B) (DayTensor A' B')
dayMap F G = factorDay (dayMapPairing F G)

dayMap-β : {A : CubicalSet ℓA} {A' : CubicalSet ℓA'} {B : CubicalSet ℓB} {B' : CubicalSet ℓB'}
  (F : CubicalNatural A A') (G : CubicalNatural B B') (p q : ℕ) (a : Cell A p) (b : Cell B q)
  → mapCells (dayMap F G) (p + q) (dayPair {A = A} {B = B} p q a b)
    ≡ dayPair {A = A'} {B = B'} p q (mapCells F p a) (mapCells G q b)
dayMap-β F G = factorDay-β (dayMapPairing F G)

dayMap-id : (A : CubicalSet ℓA) (B : CubicalSet ℓB)
  → dayMap (cubicalId A) (cubicalId B) ≡ cubicalId (DayTensor A B)
dayMap-id A B = sym (factorDay-unique (dayMapPairing (cubicalId A) (cubicalId B))
  (cubicalId (DayTensor A B)) (λ _ _ _ _ → refl))

dayMap-compose : {A : CubicalSet ℓA} {A' : CubicalSet ℓA'} {A'' : CubicalSet ℓA''}
  {B : CubicalSet ℓB} {B' : CubicalSet ℓB'} {B'' : CubicalSet ℓB''}
  (F : CubicalNatural A A') (F' : CubicalNatural A' A'')
  (G : CubicalNatural B B') (G' : CubicalNatural B' B'')
  → dayMap (F ⋆n F') (G ⋆n G') ≡ dayMap F G ⋆n dayMap F' G'
dayMap-compose F F' G G' = sym (factorDay-unique (dayMapPairing (F ⋆n F') (G ⋆n G'))
  (dayMap F G ⋆n dayMap F' G') λ p q a b →
    cong (mapCells (dayMap F' G') (p + q)) (dayMap-β F G p q a b)
    ∙ dayMap-β F' G' p q (mapCells F p a) (mapCells G q b))

postcomposePairing : {A : CubicalSet ℓA} {B : CubicalSet ℓB} {C : CubicalSet ℓC} {D : CubicalSet ℓD}
  → DayPairing A B C → CubicalNatural C D → DayPairing A B D
pairCells (postcomposePairing P F) p q a b = mapCells F (p + q) (pairCells P p q a b)
pair-natural (postcomposePairing P F) {p} {p'} {q} {q'} f g a b =
  cong (mapCells F (p + q)) (pair-natural P f g a b)
  ∙ natural F _ (pairCells P p' q' a b)

factorDay-postcompose : {A : CubicalSet ℓA} {B : CubicalSet ℓB} {C : CubicalSet ℓC} {D : CubicalSet ℓD}
  (P : DayPairing A B C) (F : CubicalNatural C D)
  → factorDay (postcomposePairing P F) ≡ factorDay P ⋆n F
factorDay-postcompose P F = sym (factorDay-unique (postcomposePairing P F) (factorDay P ⋆n F)
  (λ p q a b → cong (mapCells F (p + q)) (factorDay-β P p q a b)))

-- 这里的函子律比较真正的自然变换，非只比较顶点或零维 cell。
-- 这些定理尚不等于 monoidal category 的完整结合/单位相容性。
