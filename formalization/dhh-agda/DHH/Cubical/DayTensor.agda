{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayTensor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ; _+_)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory

private variable ℓA ℓB ℓC ℓD : Level

private
  cube-left-id : {m n : ℕ} (u : CubicalMap m n) → cubeId m ⋆c u ≡ u
  cube-left-id u = cubeMapExt (rightIdentity (underlying u))

  cube-right-id : {m n : ℕ} (u : CubicalMap m n) → u ⋆c cubeId n ≡ u
  cube-right-id u = cubeMapExt (leftIdentity (underlying u))

  cube-assoc : {k l m n : ℕ} (f : CubicalMap k l) (g : CubicalMap l m) (h : CubicalMap m n)
    → (f ⋆c g) ⋆c h ≡ f ⋆c (g ⋆c h)
  cube-assoc f g h = cubeMapExt (homExt (λ _ → refl))

-- 一个双次数配对的输入是 A_p 与 B_q，输出次数 p+q。
-- 自然性包含任意两个立方态射；不会把两输入强行放在同一维数。
record DayPairing (A : CubicalSet ℓA) (B : CubicalSet ℓB) (C : CubicalSet ℓC)
    : Type (ℓ-max ℓA (ℓ-max ℓB ℓC)) where
  field
    pairCells : (p q : ℕ) → Cell A p → Cell B q → Cell C (p + q)
    pair-natural : {p p' q q' : ℕ} (f : CubicalMap p p') (g : CubicalMap q q')
      (a : Cell A p') (b : Cell B q')
      → pairCells p q (reindex A f a) (reindex B g b)
        ≡ reindex C (f ⊗c g) (pairCells p' q' a b)
open DayPairing public

dayPairingExt : {A : CubicalSet ℓA} {B : CubicalSet ℓB} {C : CubicalSet ℓC}
  {P Q : DayPairing A B C}
  → ((p q : ℕ) (a : Cell A p) (b : Cell B q) → pairCells P p q a b ≡ pairCells Q p q a b)
  → P ≡ Q
pairCells (dayPairingExt e i) p q a b = e p q a b i
pair-natural (dayPairingExt {A = A} {B = B} {C = C} {P = P} {Q = Q} e i)
  {p} {p'} {q} {q'} f g a b = isProp→PathP
    {B = λ j → e p q (reindex A f a) (reindex B g b) j
      ≡ reindex C (f ⊗c g) (e p' q' a b j)}
    (λ j → snd (cells C (p + q)) _ _) (pair-natural P f g a b) (pair-natural Q f g a b) i

module Construction (A : CubicalSet ℓA) (B : CubicalSet ℓB) where
  -- raw 记录有限表示：两块次数、一个立方态射、两个 cell。
  -- 总体可无限；构造集合商不意味着枚举全部生成元或判定其相等。
  record Generator (n : ℕ) : Type (ℓ-max ℓA ℓB) where
    constructor raw
    field
      leftDegree rightDegree : ℕ
      chart : CubicalMap n (leftDegree + rightDegree)
      leftCell : Cell A leftDegree
      rightCell : Cell B rightDegree
  open Generator public

  -- 同时沿两侧重索引的 coend 生成关系。取一侧恒等得到单侧关系，
  -- 后面的 slide-left/slide-right 明确校正预层恒等律。
  data Slide (n : ℕ) : Generator n → Generator n → Type (ℓ-max ℓA ℓB) where
    slide : {p p' q q' : ℕ} (f : CubicalMap p p') (g : CubicalMap q q')
      (u : CubicalMap n (p + q)) (a : Cell A p') (b : Cell B q')
      → Slide n (raw p q u (reindex A f a) (reindex B g b))
        (raw p' q' (u ⋆c (f ⊗c g)) a b)

  TensorCell : ℕ → Type (ℓ-max ℓA ℓB)
  TensorCell n = Generator n SQ./ Slide n

  point : {n : ℕ} → Generator n → TensorCell n
  point = SQ.[_]

  actGenerator : {m n : ℕ} → CubicalMap m n → Generator n → Generator m
  actGenerator f (raw p q u a b) = raw p q (f ⋆c u) a b

  act-slide : {m n : ℕ} (v : CubicalMap m n) (x y : Generator n) → Slide n x y
    → point (actGenerator v x) ≡ point (actGenerator v y)
  act-slide v _ _ (slide f g u a b) =
    SQ.eq/ _ _ (slide f g (v ⋆c u) a b)
    ∙ cong (λ w → point (raw _ _ w a b)) (cube-assoc v u (f ⊗c g))

  act : {m n : ℕ} → CubicalMap m n → TensorCell n → TensorCell m
  act f = SQ.rec SQ.squash/ (λ x → point (actGenerator f x)) (act-slide f)

  tensorCubical : CubicalSet (ℓ-max ℓA ℓB)
  cells tensorCubical n = TensorCell n , SQ.squash/
  reindex tensorCubical = act
  reindex-id tensorCubical = SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ { (raw p q u a b) → cong (λ w → point (raw p q w a b)) (cube-left-id u) })
  reindex-compose tensorCubical f g = SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ { (raw p q u a b) → cong (λ w → point (raw p q w a b)) (cube-assoc f g u) })

  pair : (p q : ℕ) → Cell A p → Cell B q → TensorCell (p + q)
  pair p q a b = point (raw p q (cubeId (p + q)) a b)

  pair-naturality : {p p' q q' : ℕ} (f : CubicalMap p p') (g : CubicalMap q q')
    (a : Cell A p') (b : Cell B q')
    → pair p q (reindex A f a) (reindex B g b) ≡ act (f ⊗c g) (pair p' q' a b)
  pair-naturality {p} {p'} {q} {q'} f g a b =
    SQ.eq/ _ _ (slide f g (cubeId (p + q)) a b)
    ∙ cong (λ u → point (raw p' q' u a b))
      (cube-left-id (f ⊗c g) ∙ sym (cube-right-id (f ⊗c g)))

  slide-left : {n p p' q : ℕ} (f : CubicalMap p p') (u : CubicalMap n (p + q))
    (a : Cell A p') (b : Cell B q)
    → point (raw p q u (reindex A f a) b) ≡ point (raw p' q (u ⋆c (f ⊗c cubeId q)) a b)
  slide-left {q = q} f u a b =
    cong (λ c → point (raw _ q u (reindex A f a) c)) (sym (reindex-id B b))
    ∙ SQ.eq/ _ _ (slide f (cubeId q) u a b)

  slide-right : {n p q q' : ℕ} (g : CubicalMap q q') (u : CubicalMap n (p + q))
    (a : Cell A p) (b : Cell B q')
    → point (raw p q u a (reindex B g b)) ≡ point (raw p q' (u ⋆c (cubeId p ⊗c g)) a b)
  slide-right {p = p} g u a b =
    cong (λ c → point (raw p _ u c (reindex B g b))) (sym (reindex-id A a))
    ∙ SQ.eq/ _ _ (slide (cubeId p) g u a b)

  representative : {n : ℕ} (p q : ℕ) (u : CubicalMap n (p + q)) (a : Cell A p) (b : Cell B q)
    → point (raw p q u a b) ≡ act u (pair p q a b)
  representative p q u a b = cong (λ v → point (raw p q v a b)) (sym (cube-right-id u))

DayTensor : CubicalSet ℓA → CubicalSet ℓB → CubicalSet (ℓ-max ℓA ℓB)
DayTensor = Construction.tensorCubical

dayPair : {A : CubicalSet ℓA} {B : CubicalSet ℓB} (p q : ℕ)
  → Cell A p → Cell B q → Cell (DayTensor A B) (p + q)
dayPair {A = A} {B = B} = Construction.pair A B

dayPairing : (A : CubicalSet ℓA) (B : CubicalSet ℓB) → DayPairing A B (DayTensor A B)
pairCells (dayPairing A B) = Construction.pair A B
pair-natural (dayPairing A B) = Construction.pair-naturality A B

module _ {A : CubicalSet ℓA} {B : CubicalSet ℓB} {C : CubicalSet ℓC} (P : DayPairing A B C) where
  private module T = Construction A B

  factorGenerator : {n : ℕ} → T.Generator n → Cell C n
  factorGenerator (T.raw p q u a b) = reindex C u (pairCells P p q a b)

  factor-slide : {n : ℕ} (x y : T.Generator n) → T.Slide n x y
    → factorGenerator x ≡ factorGenerator y
  factor-slide _ _ (T.slide f g u a b) =
    cong (reindex C u) (pair-natural P f g a b)
    ∙ sym (reindex-compose C u (f ⊗c g) (pairCells P _ _ a b))

  -- 商消去只需证明生成关系上的相容。输入给出有限表示时，实际
  -- 执行是先调用配对程序，再沿 chart 重索引；不用搜索等价表示。
  factorDay : CubicalNatural (DayTensor A B) C
  mapCells factorDay n = SQ.rec (snd (cells C n)) factorGenerator factor-slide
  natural factorDay {m} u = SQ.elimProp (λ _ → snd (cells C m) _ _)
    (λ { (T.raw p q v a b) → reindex-compose C u v (pairCells P p q a b) })

  factorDay-β : (p q : ℕ) (a : Cell A p) (b : Cell B q)
    → mapCells factorDay (p + q) (dayPair {A = A} {B = B} p q a b) ≡ pairCells P p q a b
  factorDay-β p q a b = reindex-id C (pairCells P p q a b)

  -- 唯一性由商归纳及自然性给出，而不是仅提供一个满足接口的字段。
  factorDay-unique : (F : CubicalNatural (DayTensor A B) C)
    → ((p q : ℕ) (a : Cell A p) (b : Cell B q)
      → mapCells F (p + q) (dayPair {A = A} {B = B} p q a b) ≡ pairCells P p q a b)
    → F ≡ factorDay
  factorDay-unique F e = cubicalNaturalExt λ n → SQ.elimProp (λ _ → snd (cells C n) _ _)
    (λ { (T.raw p q u a b) →
      cong (mapCells F n) (T.representative p q u a b)
      ∙ natural F u (dayPair {A = A} {B = B} p q a b)
      ∙ cong (reindex C u) (e p q a b) })

pairFromNatural : {A : CubicalSet ℓA} {B : CubicalSet ℓB} {C : CubicalSet ℓC}
  → CubicalNatural (DayTensor A B) C → DayPairing A B C
pairCells (pairFromNatural {A = A} {B = B} F) p q a b =
  mapCells F (p + q) (dayPair {A = A} {B = B} p q a b)
pair-natural (pairFromNatural {A = A} {B = B} F) {p} {p'} {q} {q'} f g a b =
  cong (mapCells F (p + q)) (Construction.pair-naturality A B f g a b)
  ∙ natural F (f ⊗c g) (dayPair {A = A} {B = B} p' q' a b)

dayUniversalIso : (A : CubicalSet ℓA) (B : CubicalSet ℓB) (C : CubicalSet ℓC)
  → Iso (CubicalNatural (DayTensor A B) C) (DayPairing A B C)
Iso.fun (dayUniversalIso A B C) = pairFromNatural
Iso.inv (dayUniversalIso A B C) = factorDay
Iso.rightInv (dayUniversalIso A B C) P = dayPairingExt (factorDay-β P)
Iso.leftInv (dayUniversalIso A B C) F = sym (factorDay-unique (pairFromNatural F) F (λ _ _ _ _ → refl))

dayUniversalEquivalence : (A : CubicalSet ℓA) (B : CubicalSet ℓB) (C : CubicalSet ℓC)
  → CubicalNatural (DayTensor A B) C ≃ DayPairing A B C
dayUniversalEquivalence A B C = isoToEquiv (dayUniversalIso A B C)

-- 此处是集合值预层的实际 coend 与普遍性质。尚未在本模块构造
-- Day tensor 的结合子/单位子及其相容图，也未把 N∞ 的 lax 结构作为前提。
