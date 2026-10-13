{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayAssociatorHelpers where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor

private variable ℓA ℓB ℓC : Level

-- 固定一个外部坐标块，只改变另一个块。此处保留完整的预层律，
-- 因而随后能在内层 coend 上调用现有 factorDay，免去重复选择代表。
shiftRight : (r : ℕ) → CubicalSet ℓA → CubicalSet ℓA
cells (shiftRight r A) n = cells A (n + r)
reindex (shiftRight r A) f a = reindex A (f ⊗c cubeId r) a
reindex-id (shiftRight r A) {n} a =
  cong (λ u → reindex A u a) (tensor-id n r) ∙ reindex-id A a
reindex-compose (shiftRight r A) f g a =
  cong (λ u → reindex A u a) (tensor-right-id-compose f g r)
  ∙ reindex-compose A (f ⊗c cubeId r) (g ⊗c cubeId r) a

shiftLeft : (p : ℕ) → CubicalSet ℓA → CubicalSet ℓA
cells (shiftLeft p A) n = cells A (p + n)
reindex (shiftLeft p A) f a = reindex A (cubeId p ⊗c f) a
reindex-id (shiftLeft p A) {n} a =
  cong (λ u → reindex A u a) (tensor-id p n) ∙ reindex-id A a
reindex-compose (shiftLeft p A) f g a =
  cong (λ u → reindex A u a) (tensor-left-id-compose p f g)
  ∙ reindex-compose A (cubeId p ⊗c f) (cubeId p ⊗c g) a

dayPair-left : {A : CubicalSet ℓA} {B : CubicalSet ℓB} {p p' q : ℕ}
  (f : CubicalMap p p') (a : Cell A p') (b : Cell B q)
  → dayPair {A = A} {B = B} p q (reindex A f a) b
    ≡ reindex (DayTensor A B) (f ⊗c cubeId q) (dayPair {A = A} {B = B} p' q a b)
dayPair-left {A = A} {B} {p} {q = q} f a b =
  cong (dayPair {A = A} {B = B} p q (reindex A f a)) (sym (reindex-id B b))
  ∙ pair-natural (dayPairing A B) f (cubeId q) a b

dayPair-right : {A : CubicalSet ℓA} {B : CubicalSet ℓB} {p q q' : ℕ}
  (g : CubicalMap q q') (a : Cell A p) (b : Cell B q')
  → dayPair {A = A} {B = B} p q a (reindex B g b)
    ≡ reindex (DayTensor A B) (cubeId p ⊗c g) (dayPair {A = A} {B = B} p q' a b)
dayPair-right {A = A} {B} {p} {q} g a b =
  cong (λ z → dayPair {A = A} {B = B} p q z (reindex B g b)) (sym (reindex-id A a))
  ∙ pair-natural (dayPairing A B) (cubeId p) g a b

dayTensorExt : {A : CubicalSet ℓA} {B : CubicalSet ℓB} {C : CubicalSet ℓC}
  (F G : CubicalNatural (DayTensor A B) C)
  → ((p q : ℕ) (a : Cell A p) (b : Cell B q)
    → mapCells F (p + q) (dayPair {A = A} {B = B} p q a b)
      ≡ mapCells G (p + q) (dayPair {A = A} {B = B} p q a b))
  → F ≡ G
dayTensorExt F G e = factorDay-unique (pairFromNatural G) F e
  ∙ sym (factorDay-unique (pairFromNatural G) G (λ _ _ _ _ → refl))
