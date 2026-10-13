{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayTriple where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; _+_)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayAssociatorHelpers

private variable ℓA ℓB ℓC ℓD : Level

-- 三变量配对是 coend 消去的数据，所有实例仍须给出实际函数和
-- 重索引证明。这里没有把未知张量结合子或其相容性当作假设。
record TriplePairing (A : CubicalSet ℓA) (B : CubicalSet ℓB)
    (C : CubicalSet ℓC) (D : CubicalSet ℓD)
    : Type (ℓ-max ℓA (ℓ-max ℓB (ℓ-max ℓC ℓD))) where
  field
    triple : (p q r : ℕ) → Cell A p → Cell B q → Cell C r → Cell D ((p + q) + r)
    triple-natural : {p p' q q' r r' : ℕ}
      (f : CubicalMap p p') (g : CubicalMap q q') (h : CubicalMap r r')
      (a : Cell A p') (b : Cell B q') (c : Cell C r')
      → triple p q r (reindex A f a) (reindex B g b) (reindex C h c)
        ≡ reindex D ((f ⊗c g) ⊗c h) (triple p' q' r' a b c)
open TriplePairing public

record RightTriplePairing (A : CubicalSet ℓA) (B : CubicalSet ℓB)
    (C : CubicalSet ℓC) (D : CubicalSet ℓD)
    : Type (ℓ-max ℓA (ℓ-max ℓB (ℓ-max ℓC ℓD))) where
  field
    rightTriple : (p q r : ℕ) → Cell A p → Cell B q → Cell C r → Cell D (p + (q + r))
    rightTriple-natural : {p p' q q' r r' : ℕ}
      (f : CubicalMap p p') (g : CubicalMap q q') (h : CubicalMap r r')
      (a : Cell A p') (b : Cell B q') (c : Cell C r')
      → rightTriple p q r (reindex A f a) (reindex B g b) (reindex C h c)
        ≡ reindex D (f ⊗c (g ⊗c h)) (rightTriple p' q' r' a b c)
open RightTriplePairing public

module LeftFactor {ℓA ℓB ℓC ℓD : Level}
  (A : CubicalSet ℓA) (B : CubicalSet ℓB) (C : CubicalSet ℓC) (D : CubicalSet ℓD)
  (P : TriplePairing A B C D) where
  private module AB = Construction A B

  innerPairing : (r : ℕ) → Cell C r → DayPairing A B (shiftRight r D)
  pairCells (innerPairing r c) p q a b = triple P p q r a b c
  pair-natural (innerPairing r c) {p} {p'} {q} {q'} f g a b =
    cong (triple P p q r (reindex A f a) (reindex B g b)) (sym (reindex-id C c))
    ∙ triple-natural P f g (cubeId r) a b c

  innerFactor : (r : ℕ) → Cell C r → CubicalNatural (DayTensor A B) (shiftRight r D)
  innerFactor r c = factorDay {A = A} {B = B} {C = shiftRight r D} (innerPairing r c)

  private
    last-natural : (p q : ℕ) {r r' : ℕ} (h : CubicalMap r r')
      (a : Cell A p) (b : Cell B q) (c : Cell C r')
      → triple P p q r a b (reindex C h c)
        ≡ reindex D (cubeId (p + q) ⊗c h) (triple P p q r' a b c)
    last-natural p q {r} {r'} h a b c =
      cong₂ (λ x y → triple P p q r x y (reindex C h c))
        (sym (reindex-id A a)) (sym (reindex-id B b))
      ∙ triple-natural P (cubeId p) (cubeId q) h a b c
      ∙ cong (λ u → reindex D (u ⊗c h) (triple P p q r' a b c)) (tensor-id p q)

  -- 第二次变量自然性用内层集合商的命题消去。每次只检查 slide
  -- 生成元的公式，完全不需要挑出稳定/商元素的一个代表。
  lastFactor-natural : (s : ℕ) {r r' : ℕ} (h : CubicalMap r r')
    (ab : Cell (DayTensor A B) s) (c : Cell C r')
    → mapCells (innerFactor r (reindex C h c)) s ab
      ≡ reindex D (cubeId s ⊗c h) (mapCells (innerFactor r' c) s ab)
  lastFactor-natural s {r} {r'} h = SQ.elimProp
    (λ ab → isPropΠ (λ c → snd (cells D (s + r)) _ _))
    (λ { (AB.raw p q u a b) c →
      cong (reindex D (u ⊗c cubeId r)) (last-natural p q h a b c)
      ∙ sym (reindex-compose D (u ⊗c cubeId r) (cubeId (p + q) ⊗c h) (triple P p q r' a b c))
      ∙ cong (λ v → reindex D v (triple P p q r' a b c))
        (tensor-left-right u h ∙ sym (tensor-right-left u h))
      ∙ reindex-compose D (cubeId s ⊗c h) (u ⊗c cubeId r') (triple P p q r' a b c) })

  outerPairing : DayPairing (DayTensor A B) C D
  pairCells outerPairing s r ab c = mapCells (innerFactor r c) s ab
  pair-natural outerPairing {s} {s'} {r} {r'} f h ab c =
    natural (innerFactor r (reindex C h c)) f ab
    ∙ cong (reindex D (f ⊗c cubeId r)) (lastFactor-natural s' h ab c)
    ∙ sym (reindex-compose D (f ⊗c cubeId r) (cubeId s' ⊗c h)
      (mapCells (innerFactor r' c) s' ab))
    ∙ cong (λ u → reindex D u (mapCells (innerFactor r' c) s' ab)) (tensor-left-right f h)

  factorLeftTriple : CubicalNatural (DayTensor (DayTensor A B) C) D
  factorLeftTriple = factorDay {A = DayTensor A B} {B = C} {C = D} outerPairing

  factorLeftTriple-β : (p q r : ℕ) (a : Cell A p) (b : Cell B q) (c : Cell C r)
    → mapCells factorLeftTriple ((p + q) + r)
        (dayPair {A = DayTensor A B} {B = C} (p + q) r
          (dayPair {A = A} {B = B} p q a b) c)
      ≡ triple P p q r a b c
  factorLeftTriple-β p q r a b c =
    factorDay-β {A = DayTensor A B} {B = C} {C = D} outerPairing (p + q) r
      (dayPair {A = A} {B = B} p q a b) c
    ∙ factorDay-β {A = A} {B = B} {C = shiftRight r D} (innerPairing r c) p q a b

module RightFactor {ℓA ℓB ℓC ℓD : Level}
  (A : CubicalSet ℓA) (B : CubicalSet ℓB) (C : CubicalSet ℓC) (D : CubicalSet ℓD)
  (P : RightTriplePairing A B C D) where
  private module BC = Construction B C

  innerPairing : (p : ℕ) → Cell A p → DayPairing B C (shiftLeft p D)
  pairCells (innerPairing p a) q r b c = rightTriple P p q r a b c
  pair-natural (innerPairing p a) {q} {q'} {r} {r'} g h b c =
    cong (λ x → rightTriple P p q r x (reindex B g b) (reindex C h c)) (sym (reindex-id A a))
    ∙ rightTriple-natural P (cubeId p) g h a b c

  innerFactor : (p : ℕ) → Cell A p → CubicalNatural (DayTensor B C) (shiftLeft p D)
  innerFactor p a = factorDay {A = B} {B = C} {C = shiftLeft p D} (innerPairing p a)

  private
    first-natural : {p p' : ℕ} (f : CubicalMap p p') (q r : ℕ)
      (a : Cell A p') (b : Cell B q) (c : Cell C r)
      → rightTriple P p q r (reindex A f a) b c
        ≡ reindex D (f ⊗c cubeId (q + r)) (rightTriple P p' q r a b c)
    first-natural {p} {p'} f q r a b c =
      cong₂ (rightTriple P p q r (reindex A f a)) (sym (reindex-id B b)) (sym (reindex-id C c))
      ∙ rightTriple-natural P f (cubeId q) (cubeId r) a b c
      ∙ cong (λ u → reindex D (f ⊗c u) (rightTriple P p' q r a b c)) (tensor-id q r)

  firstFactor-natural : {p p' : ℕ} (f : CubicalMap p p') (s : ℕ)
    (a : Cell A p') (bc : Cell (DayTensor B C) s)
    → mapCells (innerFactor p (reindex A f a)) s bc
      ≡ reindex D (f ⊗c cubeId s) (mapCells (innerFactor p' a) s bc)
  firstFactor-natural {p} {p'} f s a = SQ.elimProp
    (λ bc → snd (cells D (p + s)) _ _)
    (λ { (BC.raw q r u b c) →
      cong (reindex D (cubeId p ⊗c u)) (first-natural f q r a b c)
      ∙ sym (reindex-compose D (cubeId p ⊗c u) (f ⊗c cubeId (q + r)) (rightTriple P p' q r a b c))
      ∙ cong (λ v → reindex D v (rightTriple P p' q r a b c))
        (tensor-right-left f u ∙ sym (tensor-left-right f u))
      ∙ reindex-compose D (f ⊗c cubeId s) (cubeId p' ⊗c u) (rightTriple P p' q r a b c) })

  outerPairing : DayPairing A (DayTensor B C) D
  pairCells outerPairing p s a bc = mapCells (innerFactor p a) s bc
  pair-natural outerPairing {p} {p'} {s} {s'} f g a bc =
    natural (innerFactor p (reindex A f a)) g bc
    ∙ cong (reindex D (cubeId p ⊗c g)) (firstFactor-natural f s' a bc)
    ∙ sym (reindex-compose D (cubeId p ⊗c g) (f ⊗c cubeId s')
      (mapCells (innerFactor p' a) s' bc))
    ∙ cong (λ u → reindex D u (mapCells (innerFactor p' a) s' bc)) (tensor-right-left f g)

  factorRightTriple : CubicalNatural (DayTensor A (DayTensor B C)) D
  factorRightTriple = factorDay {A = A} {B = DayTensor B C} {C = D} outerPairing

  factorRightTriple-β : (p q r : ℕ) (a : Cell A p) (b : Cell B q) (c : Cell C r)
    → mapCells factorRightTriple (p + (q + r))
        (dayPair {A = A} {B = DayTensor B C} p (q + r) a (dayPair {A = B} {B = C} q r b c))
      ≡ rightTriple P p q r a b c
  factorRightTriple-β p q r a b c =
    factorDay-β {A = A} {B = DayTensor B C} {C = D} outerPairing p (q + r) a
      (dayPair {A = B} {B = C} q r b c)
    ∙ factorDay-β {A = B} {B = C} {C = shiftLeft p D} (innerPairing p a) q r b c

module TripleExt {ℓA ℓB ℓC ℓD : Level}
  (A : CubicalSet ℓA) (B : CubicalSet ℓB) (C : CubicalSet ℓC) (D : CubicalSet ℓD) where
  private
    module AB = Construction A B
    module BC = Construction B C
    L = DayTensor (DayTensor A B) C
    R = DayTensor A (DayTensor B C)

  leftTripleExt : (F G : CubicalNatural L D)
    → ((p q r : ℕ) (a : Cell A p) (b : Cell B q) (c : Cell C r)
      → mapCells F ((p + q) + r)
          (dayPair {A = DayTensor A B} {B = C} (p + q) r (dayPair {A = A} {B = B} p q a b) c)
        ≡ mapCells G ((p + q) + r)
          (dayPair {A = DayTensor A B} {B = C} (p + q) r (dayPair {A = A} {B = B} p q a b) c))
    → F ≡ G
  leftTripleExt F G e = dayTensorExt {A = DayTensor A B} {B = C} {C = D} F G λ s r →
    SQ.elimProp (λ ab → isPropΠ (λ c → snd (cells D (s + r)) _ _))
      (λ { (AB.raw p q u a b) c →
        let t = dayPair {A = DayTensor A B} {B = C} (p + q) r
                  (dayPair {A = A} {B = B} p q a b) c
            v = u ⊗c cubeId r
            rep = cong (λ ab → dayPair {A = DayTensor A B} {B = C} s r ab c)
                    (AB.representative p q u a b)
                ∙ dayPair-left {A = DayTensor A B} {B = C} u (dayPair {A = A} {B = B} p q a b) c
        in cong (mapCells F (s + r)) rep
          ∙ natural F v t ∙ cong (reindex D v) (e p q r a b c)
          ∙ sym (natural G v t) ∙ sym (cong (mapCells G (s + r)) rep) })

  rightTripleExt : (F G : CubicalNatural R D)
    → ((p q r : ℕ) (a : Cell A p) (b : Cell B q) (c : Cell C r)
      → mapCells F (p + (q + r))
          (dayPair {A = A} {B = DayTensor B C} p (q + r) a (dayPair {A = B} {B = C} q r b c))
        ≡ mapCells G (p + (q + r))
          (dayPair {A = A} {B = DayTensor B C} p (q + r) a (dayPair {A = B} {B = C} q r b c)))
    → F ≡ G
  rightTripleExt F G e = dayTensorExt {A = A} {B = DayTensor B C} {C = D} F G λ p s a →
    SQ.elimProp (λ bc → snd (cells D (p + s)) _ _)
      (λ { (BC.raw q r u b c) →
        let t = dayPair {A = A} {B = DayTensor B C} p (q + r) a (dayPair {A = B} {B = C} q r b c)
            v = cubeId p ⊗c u
            rep = cong (dayPair {A = A} {B = DayTensor B C} p s a) (BC.representative q r u b c)
                ∙ dayPair-right {A = A} {B = DayTensor B C} u a (dayPair {A = B} {B = C} q r b c)
        in cong (mapCells F (p + s)) rep
          ∙ natural F v t ∙ cong (reindex D v) (e p q r a b c)
          ∙ sym (natural G v t) ∙ sym (cong (mapCells G (p + s)) rep) })
