{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayClosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ; _+_)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor

private variable ℓA ℓB ℓC ℓD : Level

representableMap : {m n : ℕ} → CubicalMap m n → CubicalNatural (RepresentableCube m) (RepresentableCube n)
mapCells (representableMap f) k u = u ⋆c f
natural (representableMap f) u v = Category.⋆Assoc CubeCategory u v f

representableMap-id : (n : ℕ) → representableMap (cubeId n) ≡ cubicalId (RepresentableCube n)
representableMap-id n = cubicalNaturalExt (λ k u → Category.⋆IdR CubeCategory u)

representableMap-compose : {m n k : ℕ} (f : CubicalMap m n) (g : CubicalMap n k)
  → representableMap (f ⋆c g) ≡ representableMap f ⋆n representableMap g
representableMap-compose f g = cubicalNaturalExt (λ l u → sym (Category.⋆Assoc CubeCategory u f g))

classify-reindex : (C : CubicalSet ℓC) {m n : ℕ} (f : CubicalMap m n) (c : Cell C n)
  → classifyCube C (reindex C f c) ≡ representableMap f ⋆n classifyCube C c
classify-reindex C f c = cubicalNaturalExt (λ k u → sym (reindex-compose C u f c))

-- 固定右边 A，只对左块进行重索引。两条函子律来自实际 Day coend。
dayRightId : (A : CubicalSet ℓA) {C : CubicalSet ℓC} {D : CubicalSet ℓD}
  → CubicalNatural C D → CubicalNatural (DayTensor C A) (DayTensor D A)
dayRightId A f = dayMap f (cubicalId A)

dayRightId-id : (A : CubicalSet ℓA) (C : CubicalSet ℓC)
  → dayRightId A (cubicalId C) ≡ cubicalId (DayTensor C A)
dayRightId-id A C = dayMap-id C A

dayRightId-compose : (A : CubicalSet ℓA)
  {C : CubicalSet ℓC} {D : CubicalSet ℓD} {E : CubicalSet ℓB}
  (f : CubicalNatural C D) (g : CubicalNatural D E)
  → dayRightId A (f ⋆n g) ≡ dayRightId A f ⋆n dayRightId A g
dayRightId-compose A f g =
  cong (dayMap (f ⋆n g)) (cubicalNaturalExt (λ _ _ → refl))
  ∙ dayMap-compose f g (cubicalId A) (cubicalId A)

-- 原几何 internal hom：n-cell 是 □[n]⊗A→B 的整个自然变换。
-- ⊗ 为已构造的 Day tensor；绝非逐度 Cartesian product 的指数。
DayHom : CubicalSet ℓA → CubicalSet ℓB → CubicalSet (ℓ-max ℓA ℓB)
cells (DayHom A B) n = CubicalNatural (DayTensor (RepresentableCube n) A) B , isSetCubicalNatural
reindex (DayHom A B) f h = dayRightId A (representableMap f) ⋆n h
reindex-id (DayHom A B) {n} h =
  cong (λ k → dayRightId A k ⋆n h) (representableMap-id n)
  ∙ cong (_⋆n h) (dayRightId-id A (RepresentableCube n))
  ∙ cubicalNaturalExt (λ _ _ → refl)
reindex-compose (DayHom A B) f g h =
  cong (λ k → dayRightId A k ⋆n h) (representableMap-compose f g)
  ∙ cong (_⋆n h) (dayRightId-compose A (representableMap f) (representableMap g))
  ∙ cubicalNaturalExt (λ _ _ → refl)

-- 先对输入 cell 作 Yoneda 分类，再在左块上做 DayMap。
-- 因此给定一个有限参数表示即可执行 curry，无需枚举自然变换空间。
curryDay : {C : CubicalSet ℓC} {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  → CubicalNatural (DayTensor C A) B → CubicalNatural C (DayHom A B)
mapCells (curryDay {C = C} {A = A} F) n c = dayRightId A (classifyCube C c) ⋆n F
natural (curryDay {C = C} {A = A} F) f c =
  cong (λ k → dayRightId A k ⋆n F) (classify-reindex C f c)
  ∙ cong (_⋆n F) (dayRightId-compose A (representableMap f) (classifyCube C c))
  ∙ cubicalNaturalExt (λ _ _ → refl)

-- 评价读取左块 h 的恒等参数，再送入右块 cell。自然性首先沿 Day
-- 生成元证明，最后才使用 factorDay 降商；无需假设张量结合子。
dayEvaluationPairing : (A : CubicalSet ℓA) (B : CubicalSet ℓB) → DayPairing (DayHom A B) A B
pairCells (dayEvaluationPairing A B) p q h a =
  mapCells h (p + q) (dayPair {A = RepresentableCube p} {B = A} p q (cubeId p) a)
pair-natural (dayEvaluationPairing A B) {p} {p'} {q} {q'} f g h a =
  cong (mapCells h (p + q))
    (dayMap-β (representableMap f) (cubicalId A) p q (cubeId p) (reindex A g a))
  ∙ cong (λ v → mapCells h (p + q) (dayPair {A = RepresentableCube p'} {B = A} p q v (reindex A g a)))
      (Category.⋆IdL CubeCategory f ∙ sym (Category.⋆IdR CubeCategory f))
  ∙ cong (mapCells h (p + q))
      (pair-natural (dayPairing (RepresentableCube p') A) f g (cubeId p') a)
  ∙ natural h (f ⊗c g) (dayPair {A = RepresentableCube p'} {B = A} p' q' (cubeId p') a)

dayEvaluation : (A : CubicalSet ℓA) (B : CubicalSet ℓB)
  → CubicalNatural (DayTensor (DayHom A B) A) B
dayEvaluation A B = factorDay (dayEvaluationPairing A B)

uncurryDayPairing : {C : CubicalSet ℓC} {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  → CubicalNatural C (DayHom A B) → DayPairing C A B
pairCells (uncurryDayPairing {A = A} {B = B} h) p q c a =
  pairCells (dayEvaluationPairing A B) p q (mapCells h p c) a
pair-natural (uncurryDayPairing {A = A} {B = B} h) {p} {p'} {q} {q'} f g c a =
  cong (λ k → pairCells (dayEvaluationPairing A B) p q k (reindex A g a)) (natural h f c)
  ∙ pair-natural (dayEvaluationPairing A B) f g (mapCells h p' c) a

uncurryDay : {C : CubicalSet ℓC} {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  → CubicalNatural C (DayHom A B) → CubicalNatural (DayTensor C A) B
uncurryDay h = factorDay (uncurryDayPairing h)

uncurryDay-β : {C : CubicalSet ℓC} {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  (h : CubicalNatural C (DayHom A B)) (p q : ℕ) (c : Cell C p) (a : Cell A q)
  → mapCells (uncurryDay h) (p + q) (dayPair {A = C} {B = A} p q c a)
    ≡ mapCells (mapCells h p c) (p + q) (dayPair {A = RepresentableCube p} {B = A} p q (cubeId p) a)
uncurryDay-β h = factorDay-β (uncurryDayPairing h)

private
  dayTransformExt : {C : CubicalSet ℓC} {A : CubicalSet ℓA} {B : CubicalSet ℓB}
    (F G : CubicalNatural (DayTensor C A) B)
    → ((p q : ℕ) (c : Cell C p) (a : Cell A q)
      → mapCells F (p + q) (dayPair {A = C} {B = A} p q c a)
        ≡ mapCells G (p + q) (dayPair {A = C} {B = A} p q c a))
    → F ≡ G
  dayTransformExt F G e = factorDay-unique (pairFromNatural G) F e
    ∙ sym (factorDay-unique (pairFromNatural G) G (λ _ _ _ _ → refl))

uncurry-curryDay : {C : CubicalSet ℓC} {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  (F : CubicalNatural (DayTensor C A) B)
  → uncurryDay (curryDay F) ≡ F
uncurry-curryDay {C = C} {A = A} {B = B} F =
  dayTransformExt {C = C} {A = A} {B = B} (uncurryDay (curryDay F)) F λ p q c a →
    uncurryDay-β (curryDay F) p q c a
    ∙ cong (mapCells F (p + q)) (dayMap-β (classifyCube C c) (cubicalId A) p q (cubeId p) a)
    ∙ cong (λ d → mapCells F (p + q) (dayPair {A = C} {B = A} p q d a)) (reindex-id C c)

curry-uncurryDay : {C : CubicalSet ℓC} {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  (h : CubicalNatural C (DayHom A B))
  → curryDay (uncurryDay h) ≡ h
curry-uncurryDay {C = C} {A = A} {B = B} h = cubicalNaturalExt λ n c →
  dayTransformExt {C = RepresentableCube n} {A = A} {B = B}
    (dayRightId A (classifyCube C c) ⋆n uncurryDay h) (mapCells h n c) λ p q f a →
      cong (mapCells (uncurryDay h) (p + q)) (dayMap-β (classifyCube C c) (cubicalId A) p q f a)
      ∙ uncurryDay-β h p q (reindex C f c) a
      ∙ cong (λ k → mapCells k (p + q) (dayPair {A = RepresentableCube p} {B = A} p q (cubeId p) a))
          (natural h f c)
      ∙ cong (mapCells (mapCells h n c) (p + q))
          (dayMap-β (representableMap f) (cubicalId A) p q (cubeId p) a)
      ∙ cong (λ v → mapCells (mapCells h n c) (p + q) (dayPair {A = RepresentableCube n} {B = A} p q v a))
          (Category.⋆IdL CubeCategory f)

dayClosedIso : (C : CubicalSet ℓC) (A : CubicalSet ℓA) (B : CubicalSet ℓB)
  → Iso (CubicalNatural (DayTensor C A) B) (CubicalNatural C (DayHom A B))
Iso.fun (dayClosedIso C A B) = curryDay
Iso.inv (dayClosedIso C A B) = uncurryDay
Iso.rightInv (dayClosedIso C A B) = curry-uncurryDay
Iso.leftInv (dayClosedIso C A B) = uncurry-curryDay

dayClosedEquivalence : (C : CubicalSet ℓC) (A : CubicalSet ℓA) (B : CubicalSet ℓB)
  → CubicalNatural (DayTensor C A) B ≃ CubicalNatural C (DayHom A B)
dayClosedEquivalence C A B = isoToEquiv (dayClosedIso C A B)

-- 已证的是几何张量的实际闭合伴随，适用于任意集合值立方预层。
-- 这不自动证明 DayHom 的 Kan 性或原 DHH 的准范畴比较定理。
