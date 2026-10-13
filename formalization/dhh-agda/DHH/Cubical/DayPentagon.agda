{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayPentagon where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; _+_)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.Cubes using (Q)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCategory.Coordinates
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.Cubical.DayAssociatorHelpers
open import DHH.Cubical.DayTriple
open import DHH.Cubical.DayAssociator

private variable ℓA ℓB ℓC ℓD ℓE : Level

rightQuadHomExt : {p q r s k : ℕ} {f g : Hom (Q (p + (q + (r + s)))) (Q k)}
  → ((x : Vertex (Q p)) (y : Vertex (Q q)) (z : Vertex (Q r)) (w : Vertex (Q s))
    → onVertices f (appendPoint p (q + (r + s)) x (appendPoint q (r + s) y (appendPoint r s z w)))
      ≡ onVertices g (appendPoint p (q + (r + s)) x (appendPoint q (r + s) y (appendPoint r s z w))))
  → f ≡ g
rightQuadHomExt {p} {q} {r} {s} {k} {f} {g} e =
  rightTripleHomExt {p = p} {q = q} {r = r + s} {k = k} {f = f} {g = g} λ x y zw →
    sym (cong (λ t → onVertices f (appendPoint p (q + (r + s)) x (appendPoint q (r + s) y t)))
      (append-split r s zw))
    ∙ e x y (fst (splitPoint r s zw)) (snd (splitPoint r s zw))
    ∙ cong (λ t → onVertices g (appendPoint p (q + (r + s)) x (appendPoint q (r + s) y t)))
      (append-split r s zw)

-- 两条路线只是重新括号，坐标既不交换也不丢失。分块外延性
-- 由递归 split/append 推出，因此这里覆盖任意四块次数。
dayPentagon-chart : (p q r s : ℕ)
  → (cubeId p ⊗c cubeAssociatorInv q r s)
      ⋆c (cubeAssociatorInv p (q + r) s ⋆c (cubeAssociatorInv p q r ⊗c cubeId s))
    ≡ cubeAssociatorInv p q (r + s) ⋆c cubeAssociatorInv (p + q) r s
dayPentagon-chart p q r s = cubeMapExt
  (rightQuadHomExt {p = p} {q = q} {r = r} {s = s} {k = ((p + q) + r) + s}
    {f = underlying ((cubeId p ⊗c cubeAssociatorInv q r s)
      ⋆c (cubeAssociatorInv p (q + r) s ⋆c (cubeAssociatorInv p q r ⊗c cubeId s)))}
    {g = underlying (cubeAssociatorInv p q (r + s) ⋆c cubeAssociatorInv (p + q) r s)} λ x y z w →
    let a = cubeId p ⊗c cubeAssociatorInv q r s
        b = cubeAssociatorInv p (q + r) s
        c = cubeAssociatorInv p q r ⊗c cubeId s
        d = cubeAssociatorInv p q (r + s)
        e = cubeAssociatorInv (p + q) r s
        first = tensor-on-append (cubeId p) (cubeAssociatorInv q r s) x
                  (appendPoint q (r + s) y (appendPoint r s z w))
              ∙ cong (appendPoint p ((q + r) + s) x) (cubeAssociatorInv-on-append q r s y z w)
        second = cong (onVertices (underlying b)) first
               ∙ cubeAssociatorInv-on-append p (q + r) s x (appendPoint q r y z) w
        long = cong (onVertices (underlying c)) second
             ∙ tensor-on-append (cubeAssociatorInv p q r) (cubeId s)
                 (appendPoint p (q + r) x (appendPoint q r y z)) w
             ∙ cong (λ t → appendPoint ((p + q) + r) s t w) (cubeAssociatorInv-on-append p q r x y z)
        short = cong (onVertices (underlying e))
                  (cubeAssociatorInv-on-append p q (r + s) x y (appendPoint r s z w))
              ∙ cubeAssociatorInv-on-append (p + q) r s (appendPoint p q x y) z w
    in long ∙ sym short)

rightQuadCell : (A : CubicalSet ℓA) (B : CubicalSet ℓB) (C : CubicalSet ℓC) (D : CubicalSet ℓD)
  (p q r s : ℕ) → Cell A p → Cell B q → Cell C r → Cell D s
  → Cell (DayTensor A (DayTensor B (DayTensor C D))) (p + (q + (r + s)))
rightQuadCell A B C D p q r s a b c d = rightTripleCell A B (DayTensor C D) p q (r + s) a b
  (dayPair {A = C} {B = D} r s c d)

module _ (A : CubicalSet ℓA) (B : CubicalSet ℓB) (C : CubicalSet ℓC) (D : CubicalSet ℓD)
  (E : CubicalSet ℓE) where
  private module CD = Construction C D

  rightQuadExt : (F G : CubicalNatural (DayTensor A (DayTensor B (DayTensor C D))) E)
    → ((p q r s : ℕ) (a : Cell A p) (b : Cell B q) (c : Cell C r) (d : Cell D s)
      → mapCells F (p + (q + (r + s))) (rightQuadCell A B C D p q r s a b c d)
        ≡ mapCells G (p + (q + (r + s))) (rightQuadCell A B C D p q r s a b c d))
    → F ≡ G
  rightQuadExt F G e = TripleExt.rightTripleExt A B (DayTensor C D) E F G λ p q t a b →
    SQ.elimProp (λ cd → snd (cells E (p + (q + t))) _ _)
      (λ { (CD.raw r s u c d) →
        let x = rightQuadCell A B C D p q r s a b c d
            v = cubeId p ⊗c (cubeId q ⊗c u)
            rep = cong (rightTripleCell A B (DayTensor C D) p q t a b) (CD.representative r s u c d)
                ∙ cong (dayPair {A = A} {B = DayTensor B (DayTensor C D)} p (q + t) a)
                    (dayPair-right {A = B} {B = DayTensor C D} u b (dayPair {A = C} {B = D} r s c d))
                ∙ dayPair-right {A = A} {B = DayTensor B (DayTensor C D)} (cubeId q ⊗c u) a
                    (dayPair {A = B} {B = DayTensor C D} q (r + s) b (dayPair {A = C} {B = D} r s c d))
        in cong (mapCells F (p + (q + t))) rep
          ∙ natural F v x ∙ cong (reindex E v) (e p q r s a b c d)
          ∙ sym (natural G v x) ∙ sym (cong (mapCells G (p + (q + t))) rep) })

module _ (A : CubicalSet ℓA) (B : CubicalSet ℓB) (C : CubicalSet ℓC) (D : CubicalSet ℓD) where
  private
    T = DayTensor (DayTensor (DayTensor A B) C) D
    Q₁ = DayTensor A (DayTensor (DayTensor B C) D)
    Q₂ = DayTensor (DayTensor A (DayTensor B C)) D
    Q₄ = DayTensor (DayTensor A B) (DayTensor C D)
    step₁ = dayMap (cubicalId A) (dayAssociatorInv B C D)
    step₂ = dayAssociatorInv A (DayTensor B C) D
    step₃ = dayMap (dayAssociatorInv A B C) (cubicalId D)
    step₄ = dayAssociatorInv A B (DayTensor C D)
    step₅ = dayAssociatorInv (DayTensor A B) C D

  dayPentagon : (step₁ ⋆n step₂) ⋆n step₃ ≡ step₄ ⋆n step₅
  dayPentagon = rightQuadExt A B C D T _ _ λ p q r s a b c d →
    let x = rightQuadCell A B C D p q r s a b c d
        ab = dayPair {A = A} {B = B} p q a b
        bc = dayPair {A = B} {B = C} q r b c
        cd = dayPair {A = C} {B = D} r s c d
        x₁ = rightTripleCell A (DayTensor B C) D p (q + r) s a bc d
        x₂ = leftTripleCell A (DayTensor B C) D p (q + r) s a bc d
        x₄ = rightTripleCell (DayTensor A B) C D (p + q) r s ab c d
        y = leftTripleCell (DayTensor A B) C D (p + q) r s ab c d
        u₁ = cubeId p ⊗c cubeAssociatorInv q r s
        u₂ = cubeAssociatorInv p (q + r) s
        u₃ = cubeAssociatorInv p q r ⊗c cubeId s
        u₄ = cubeAssociatorInv p q (r + s)
        u₅ = cubeAssociatorInv (p + q) r s
        β₁ = dayMap-β (cubicalId A) (dayAssociatorInv B C D) p (q + (r + s)) a
                (rightTripleCell B C D q r s b c d)
             ∙ cong (dayPair {A = A} {B = DayTensor (DayTensor B C) D} p (q + (r + s)) a)
                 (dayAssociatorInv-β B C D q r s b c d)
             ∙ dayPair-right {A = A} {B = DayTensor (DayTensor B C) D}
                 (cubeAssociatorInv q r s) a (leftTripleCell B C D q r s b c d)
        β₂ = dayAssociatorInv-β A (DayTensor B C) D p (q + r) s a bc d
        β₃ = dayMap-β (dayAssociatorInv A B C) (cubicalId D) (p + (q + r)) s
                (rightTripleCell A B C p q r a b c) d
             ∙ cong (λ t → dayPair {A = DayTensor (DayTensor A B) C} {B = D} (p + (q + r)) s t d)
                 (dayAssociatorInv-β A B C p q r a b c)
             ∙ dayPair-left {A = DayTensor (DayTensor A B) C} {B = D}
                 (cubeAssociatorInv p q r) (leftTripleCell A B C p q r a b c) d
        β₄ = dayAssociatorInv-β A B (DayTensor C D) p q (r + s) a b cd
        β₅ = dayAssociatorInv-β (DayTensor A B) C D (p + q) r s ab c d
        long = cong (λ t → mapCells step₃ (p + (q + (r + s))) (mapCells step₂ (p + (q + (r + s))) t)) β₁
             ∙ cong (mapCells step₃ (p + (q + (r + s)))) (natural step₂ u₁ x₁)
             ∙ natural step₃ u₁ (mapCells step₂ (p + ((q + r) + s)) x₁)
             ∙ cong (reindex T u₁)
                 (cong (mapCells step₃ (p + ((q + r) + s))) β₂
                 ∙ natural step₃ u₂ x₂
                 ∙ cong (reindex T u₂) β₃
                 ∙ sym (reindex-compose T u₂ u₃ y))
             ∙ sym (reindex-compose T u₁ (u₂ ⋆c u₃) y)
        short = cong (mapCells step₅ (p + (q + (r + s)))) β₄
              ∙ natural step₅ u₄ x₄
              ∙ cong (reindex T u₄) β₅
              ∙ sym (reindex-compose T u₄ u₅ y)
    in long ∙ cong (λ u → reindex T u y) (dayPentagon-chart p q r s) ∙ sym short
