{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.IntegerCubical where

-- 先把已证的各维 Iso 运输为预层，并明确命名 transportedIntegerNerve。
-- 下面另将各个生成算子识别为整数坐标上的直接公式；运输本身
-- 不能替代这些识别，也不提供 Kan 填充或任意图的同伦类型实现。

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-comm)
open import Cubical.Data.Int using (ℤ) renaming (min to minℤ; max to maxℤ)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.GraphSets
open import DHH.Cubes using (Position; here; there; boxHom)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Interval using (endpoint; minFin; maxFin)
open import DHH.StableNerve.Nerve using (Nₘ; gridAction; gridAction-word)
open import DHH.StableNerve.Colimit
open import DHH.StableNerve.CenteredInterval
open import DHH.StableNerve.IntegerInterval
open import DHH.StableNerve.IntegerStable
open import DHH.StableNerve.IntegerDirections using
  (scalarProjection; clipCoordinate; CoordinateWindow; all-to-coordinates;
   scalar-lower-ray; scalar-upper-ray; replaceCoordinate)
open import DHH.StableNerve.IntegerPaperStability
open import DHH.StableNerve.IntegerLattice

private variable ℓ ℓ' : Level

paperIntegerCell-isSet : (G : Graph ℓ) (n : ℕ) → isSet (PaperIntegerCell G n)
paperIntegerCell-isSet G n = isSetΣSndProp isSetGraphHom (λ f → paperStable-isProp f)

module Transported {ℓ : Level} (G : Graph ℓ) where
  cellIso : (n : ℕ) → Iso (Cell (N∞ G) n) (PaperIntegerCell G n)
  cellIso = colimitPaperCellIso G

  -- 完整预层结构来自实际已证的 Iso；不是要求调用者给任意结构。
  transportedIntegerNerve : CubicalSet ℓ
  cells transportedIntegerNerve n = PaperIntegerCell G n , paperIntegerCell-isSet G n
  reindex transportedIntegerNerve {m} {n} u c =
    Iso.fun (cellIso m) (reindex (N∞ G) u (Iso.inv (cellIso n) c))
  reindex-id transportedIntegerNerve {n} c =
    cong (Iso.fun (cellIso n)) (reindex-id (N∞ G) (Iso.inv (cellIso n) c)) ∙ Iso.rightInv (cellIso n) c
  reindex-compose transportedIntegerNerve {m} {n} {k} u v c =
    cong (Iso.fun (cellIso m)) (reindex-compose (N∞ G) u v (Iso.inv (cellIso k) c))
    ∙ sym (cong (λ d → Iso.fun (cellIso m) (reindex (N∞ G) u d))
      (Iso.leftInv (cellIso n) (reindex (N∞ G) v (Iso.inv (cellIso k) c))))

  toInteger : CubicalNatural (N∞ G) transportedIntegerNerve
  mapCells toInteger n = Iso.fun (cellIso n)
  natural toInteger {m} {n} u c = sym (cong
    (λ d → Iso.fun (cellIso m) (reindex (N∞ G) u d)) (Iso.leftInv (cellIso n) c))

  fromInteger : CubicalNatural transportedIntegerNerve (N∞ G)
  mapCells fromInteger n = Iso.inv (cellIso n)
  natural fromInteger {m} {n} u c =
    Iso.leftInv (cellIso m) (reindex (N∞ G) u (Iso.inv (cellIso n) c))

  from-to : toInteger ⋆n fromInteger ≡ cubicalId (N∞ G)
  from-to = cubicalNaturalExt (λ n → Iso.leftInv (cellIso n))

  to-from : fromInteger ⋆n toInteger ≡ cubicalId transportedIntegerNerve
  to-from = cubicalNaturalExt (λ n → Iso.rightInv (cellIso n))

open Transported public using (transportedIntegerNerve; toInteger; fromInteger)

transportedGraphMap : {G : Graph ℓ} {H : Graph ℓ'} (h : Hom G H)
  → CubicalNatural (transportedIntegerNerve G) (transportedIntegerNerve H)
transportedGraphMap {G = G} {H = H} h = fromInteger G ⋆n N∞-map h ⋆n toInteger H

transportedGraphMap-formula : {G : Graph ℓ} {H : Graph ℓ'} (h : Hom G H) (n : ℕ)
  (c : PaperIntegerCell G n) → mapCells (transportedGraphMap h) n c ≡ paperIntegerMap h n c
transportedGraphMap-formula {G = G} h n c =
  colimitPaperCell-natural h n (Iso.inv (colimitPaperCellIso G n) c)
    ∙ cong (paperIntegerMap h n) (Iso.rightInv (colimitPaperCellIso G n) c)

insertInteger : {n : ℕ} → Position (suc n) → ℤ
  → Vertex (IntegerGrid n) → Vertex (IntegerGrid (suc n))
insertInteger here z x = z , x
insertInteger {suc n} (there i) z (a , x) = a , insertInteger i z x

deleteInteger : {n : ℕ} → Position (suc n)
  → Vertex (IntegerGrid (suc n)) → Vertex (IntegerGrid n)
deleteInteger here (z , x) = x
deleteInteger {suc n} (there i) (z , x) = z , deleteInteger i x

integerFaceAt : {n : ℕ} → Position (suc n) → ℤ
  → Hom (IntegerGrid n) (IntegerGrid (suc n))
onVertices (integerFaceAt i z) = insertInteger i z
preserves (integerFaceAt here z) e = ∣ inl (refl , e) ∣₁
preserves (integerFaceAt {suc n} (there i) z) e =
  preserves (boxHom (idHom Iℤ) (integerFaceAt i z)) e

integerDelete : {n : ℕ} → Position (suc n) → Hom (IntegerGrid (suc n)) (IntegerGrid n)
onVertices (integerDelete i) = deleteInteger i
preserves (integerDelete {n} here) {x = (a , u)} {y = (b , v)} =
  PT.rec (adj-isProp (IntegerGrid n) u v) λ where
    (inl (p , e)) → e
    (inr (e , p)) → subst (Adj (IntegerGrid n) u) p (adj-refl (IntegerGrid n) u)
preserves (integerDelete {suc n} (there i)) e =
  preserves (boxHom (idHom Iℤ) (integerDelete i)) e

clamp-delete : {n : ℕ} (k : ℕ) (i : Position (suc n)) (x : Vertex (IntegerGrid (suc n)))
  → onVertices (centeredClampGrid k n) (deleteInteger i x)
    ≡ deleteGrid (suc k) i (onVertices (centeredClampGrid k (suc n)) x)
clamp-delete k here (a , x) = refl
clamp-delete {suc n} k (there i) (a , x) =
  cong (λ y → onVertices (centeredClamp k) a , y) (clamp-delete k i x)

-- 直接退化公式就是删去该整数坐标，然后调用原图映射。
-- 首先对每个有限窗口证明，再由集合商归纳推广到所有 stable cells。
degeneracy-formula-on-stage : {G : Graph ℓ} {n : ℕ} (k : ℕ)
  (i : Position (suc n)) (f : Hom (Grid (suc k) n) G)
  → centeredExtend k (suc n) (f ∘g gridDelete (suc k) i)
    ≡ centeredExtend k n f ∘g integerDelete i
degeneracy-formula-on-stage k i f = homExt (λ x →
  cong (onVertices f) (sym (clamp-delete k i x)))

integer-degeneracy-comparison : {G : Graph ℓ} {n : ℕ} (i : Position (suc n))
  (c : Cell (N∞ G) n)
  → IntegerComparison.integerHom G (suc n) (reindex (N∞ G) (cubeDelete i) c)
    ≡ IntegerComparison.integerHom G n c ∘g integerDelete i
integer-degeneracy-comparison {G = G} i = SQ.elimProp (λ _ → isSetGraphHom _ _)
  (λ { (k , f) → degeneracy-formula-on-stage k i f })

transported-degeneracy-formula : {G : Graph ℓ} {n : ℕ} (i : Position (suc n))
  (c : PaperIntegerCell G n)
  → fst (reindex (transportedIntegerNerve G) (cubeDelete i) c)
    ≡ fst c ∘g integerDelete i
transported-degeneracy-formula {G = G} {n} i c =
  integer-degeneracy-comparison i (Iso.inv (colimitPaperCellIso G n) c)
    ∙ cong (λ h → h ∘g integerDelete i)
      (cong fst (Iso.rightInv (colimitPaperCellIso G n) c))

centeredEndpoint : (k : ℕ) → Bool → ℤ
centeredEndpoint k b = onVertices (centeredInclusion k) (endpoint (suc k) b)

clamp-insert : {n : ℕ} (k : ℕ) (i : Position (suc n)) (b : Bool)
  (x : Vertex (IntegerGrid n))
  → onVertices (centeredClampGrid k (suc n)) (insertInteger i (centeredEndpoint k b) x)
    ≡ insertGrid (suc k) i b (onVertices (centeredClampGrid k n) x)
clamp-insert {n} k here b x = cong (λ a → a , onVertices (centeredClampGrid k n) x)
  (cong (λ h → onVertices h (endpoint (suc k) b)) (centered-retraction k))
clamp-insert {suc n} k (there i) b (a , x) =
  cong (λ y → onVertices (centeredClamp k) a , y) (clamp-insert k i b x)

face-formula-on-stage : {G : Graph ℓ} {n : ℕ} (k : ℕ)
  (i : Position (suc n)) (b : Bool) (f : Hom (Grid (suc k) (suc n)) G)
  → centeredExtend k n (f ∘g gridFace (suc k) i b)
    ≡ centeredExtend k (suc n) f ∘g integerFaceAt i (centeredEndpoint k b)
face-formula-on-stage k i b f = homExt (λ x →
  cong (onVertices f) (sym (clamp-insert k i b x)))

-- 任意给定的稳定窗口都恢复同一个 paper cell；这里没有挑规范阶段。
paper-cell-from-window : {G : Graph ℓ} (n k : ℕ) (c : PaperIntegerCell G n)
  → fst c ∘g windowProjection k n ≡ fst c
  → Iso.fun (colimitPaperCellIso G n)
      (mapCells (includeStage G k) n (centeredRestrict k n (fst c))) ≡ c
paper-cell-from-window n k c p = Σ≡Prop (λ f → paperStable-isProp f) p

-- 面公式：在任意稳定窗口的相应端点取值。下一段进一步以唯一的
-- 整数半直线极限定义直接 face，确保这不是仅给运输结构改名。
transported-face-at-window : {G : Graph ℓ} {n : ℕ} (k : ℕ)
  (i : Position (suc n)) (b : Bool) (c : PaperIntegerCell G (suc n))
  → fst c ∘g windowProjection k (suc n) ≡ fst c
  → fst (reindex (transportedIntegerNerve G) (cubeFace i b) c)
    ≡ fst c ∘g integerFaceAt i (centeredEndpoint k b)
transported-face-at-window {G = G} {n} k i b c p =
  cong (λ d → fst (reindex (transportedIntegerNerve G) (cubeFace i b) d))
    (sym (paper-cell-from-window (suc n) k c p))
  ∙ sym (cong fst (natural (toInteger G) (cubeFace i b)
    (mapCells (includeStage G k) (suc n) (centeredRestrict k (suc n) (fst c)))))
  ∙ face-formula-on-stage k i b (centeredRestrict k (suc n) (fst c))
  ∙ cong (λ h → h ∘g integerFaceAt i (centeredEndpoint k b)) p

positionFin : {n : ℕ} → Position n → Fin n
positionFin here = fzero
positionFin (there i) = fsuc (positionFin i)

replace-insert : {n : ℕ} (i : Position (suc n)) (z w : ℤ) (x : Vertex (IntegerGrid n))
  → replaceCoordinate (positionFin i) z (insertInteger i w x) ≡ insertInteger i z x
replace-insert here z w x = refl
replace-insert {suc n} (there i) z w (a , x) = cong (λ y → a , y) (replace-insert i z w x)

clip-insert : {n : ℕ} (k : ℕ) (i : Position (suc n)) (z : ℤ) (x : Vertex (IntegerGrid n))
  → clipCoordinate k (positionFin i) (insertInteger i z x)
    ≡ insertInteger i (scalarProjection k z) x
clip-insert k here z x = refl
clip-insert {suc n} k (there i) z (a , x) = cong (λ y → a , y) (clip-insert k i z x)

record EndpointWitness {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid (suc n)) G)
  (i : Position (suc n)) (b : Bool) (r : Hom (IntegerGrid n) G) : Type ℓ where
  field
    endpointBound : ℕ
    onRay : (d : ℕ) (x : Vertex (IntegerGrid n))
      → onVertices r x ≡ onVertices f (insertInteger i (signed b (endpointBound + d)) x)
open EndpointWitness public

IsEndpointLimit : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid (suc n)) G)
  (i : Position (suc n)) (b : Bool) → Hom (IntegerGrid n) G → Type ℓ
IsEndpointLimit f i b r = ∥ EndpointWitness f i b r ∥₁

-- 两个最终常值公式在 M+L 处相遇。此证明仅取有限的共同阈值，
-- 不假定任意整数序列有极限，也不使用选择公理。
endpoint-unique : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid (suc n)) G)
  (i : Position (suc n)) (b : Bool) (r s : Hom (IntegerGrid n) G)
  → IsEndpointLimit f i b r → IsEndpointLimit f i b s → r ≡ s
endpoint-unique f i b r s = PT.rec (isPropΠ (λ _ → isSetGraphHom r s))
  λ p → PT.rec (isSetGraphHom r s) λ q → homExt λ x →
    onRay p (endpointBound q) x
      ∙ cong (λ t → onVertices f (insertInteger i (signed b t) x))
        (+-comm (endpointBound p) (endpointBound q))
      ∙ sym (onRay q (endpointBound p) x)

EndpointCandidate : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid (suc n)) G)
  (i : Position (suc n)) (b : Bool) → Type ℓ
EndpointCandidate {G = G} {n} f i b = Σ[ r ∈ Hom (IntegerGrid n) G ] IsEndpointLimit f i b r

endpointCandidate-isProp : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid (suc n)) G)
  (i : Position (suc n)) (b : Bool) → isProp (EndpointCandidate f i b)
endpointCandidate-isProp f i b (r , p) (s , q) =
  Σ≡Prop (λ _ → squash₁) (endpoint-unique f i b r s p q)

-- 直接的稳定端点操作：从论文给定的方向阈值构造图映射，
-- 以极限唯一性消去截断。定义不调用运输的 cubical reindex。
directEndpoint : {G : Graph ℓ} {n : ℕ} (c : PaperIntegerCell G (suc n))
  (i : Position (suc n)) (b : Bool) → EndpointCandidate (fst c) i b
directEndpoint (f , p) i b = PT.rec (endpointCandidate-isProp f i b)
  (λ { (M , q) → f ∘g integerFaceAt i (signed b M) ,
    ∣ record { endpointBound = M ; onRay = λ d x →
      sym (cong (onVertices f) (sym (replace-insert i (signed b (M + d)) (signed b M) x))
        ∙ q d (insertInteger i (signed b M) x)
        ∙ cong (onVertices f) (replace-insert i (signed b M) (signed b M) x)) } ∣₁ })
  (p (positionFin i) b)

directFaceHom : {G : Graph ℓ} {n : ℕ} → PaperIntegerCell G (suc n)
  → Position (suc n) → Bool → Hom (IntegerGrid n) G
directFaceHom c i b = fst (directEndpoint c i b)

endpoint-from-direction : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid (suc n)) G)
  (i : Position (suc n)) (b : Bool) (M : ℕ)
  → DirectionData (onVertices f) (positionFin i) b M
  → IsEndpointLimit f i b (f ∘g integerFaceAt i (signed b M))
endpoint-from-direction f i b M q =
  ∣ record { endpointBound = M ; onRay = λ d x →
    sym (cong (onVertices f) (sym (replace-insert i (signed b (M + d)) (signed b M) x))
      ∙ q d (insertInteger i (signed b M) x)
      ∙ cong (onVertices f) (replace-insert i (signed b M) (signed b M) x)) } ∣₁

-- 与论文完全相同的面公式：任何合法方向阈值 M 都给同一结果。
direct-face-at-threshold : {G : Graph ℓ} {n : ℕ} (c : PaperIntegerCell G (suc n))
  (i : Position (suc n)) (b : Bool) (M : ℕ)
  → DirectionData (onVertices (fst c)) (positionFin i) b M
  → directFaceHom c i b ≡ fst c ∘g integerFaceAt i (signed b M)
direct-face-at-threshold c i b M q = endpoint-unique (fst c) i b _ _
  (snd (directEndpoint c i b)) (endpoint-from-direction (fst c) i b M q)

endpointWindowBound : ℕ → Bool → ℕ
endpointWindowBound k false = suc (offset k)
endpointWindowBound k true = suc k

window-endpoint-saturation : (k : ℕ) (b : Bool) (d : ℕ)
  → scalarProjection k (signed b (endpointWindowBound k b + d)) ≡ centeredEndpoint k b
window-endpoint-saturation k false d =
  cong (scalarProjection k) (sym (down-negative (offset k) d)) ∙ scalar-lower-ray k d
window-endpoint-saturation k true d =
  cong (scalarProjection k) (sym (positive-upper-ray (offset k) (suc k) d))
  ∙ scalar-upper-ray k (offset k + d)
  ∙ sym (cong (down (offset k)) (finiteToInteger-top (suc k)))

window-endpoint-limit : {G : Graph ℓ} {n : ℕ} (k : ℕ)
  (f : Hom (IntegerGrid (suc n)) G) (p : f ∘g windowProjection k (suc n) ≡ f)
  (i : Position (suc n)) (b : Bool)
  → IsEndpointLimit f i b (f ∘g integerFaceAt i (centeredEndpoint k b))
window-endpoint-limit {n = n} k f p i b =
  ∣ record { endpointBound = endpointWindowBound k b ; onRay = λ d x →
    sym (q (positionFin i) (insertInteger i (signed b (endpointWindowBound k b + d)) x)
      ∙ cong (onVertices f) (clip-insert k i (signed b (endpointWindowBound k b + d)) x)
      ∙ cong (λ z → onVertices f (insertInteger i z x)) (window-endpoint-saturation k b d)) } ∣₁
  where
  q : CoordinateWindow {n = suc n} k (onVertices f)
  q = all-to-coordinates k (suc n) (onVertices f) (λ x → cong (λ h → onVertices h x) p)

transported-face-is-limit : {G : Graph ℓ} {n : ℕ} (c : PaperIntegerCell G (suc n))
  (i : Position (suc n)) (b : Bool)
  → IsEndpointLimit (fst c) i b
      (fst (reindex (transportedIntegerNerve G) (cubeFace i b) c))
transported-face-is-limit c i b = PT.rec squash₁ (λ { (k , p) →
  subst (IsEndpointLimit (fst c) i b)
    (sym (transported-face-at-window k i b c p))
    (window-endpoint-limit k (fst c) p i b) })
  (paper-to-window-stable (fst c) (snd c))

transported-face-formula : {G : Graph ℓ} {n : ℕ} (c : PaperIntegerCell G (suc n))
  (i : Position (suc n)) (b : Bool)
  → fst (reindex (transportedIntegerNerve G) (cubeFace i b) c) ≡ directFaceHom c i b
transported-face-formula c i b = endpoint-unique (fst c) i b _ _
  (transported-face-is-limit c i b) (snd (directEndpoint c i b))

mergeInteger : {n : ℕ} → Position (suc n) → (ℤ → ℤ → ℤ)
  → Vertex (IntegerGrid (suc (suc n))) → Vertex (IntegerGrid (suc n))
mergeInteger here op (a , b , x) = op a b , x
mergeInteger {suc n} (there i) op (a , x) = a , mergeInteger i op x

integerConnection : {n : ℕ} (i : Position (suc n)) (op : ℤ → ℤ → ℤ)
  (left : {a a' : ℤ} → IntegerNear a a' → (b : ℤ) → IntegerNear (op a b) (op a' b))
  (right : (a : ℤ) {b b' : ℤ} → IntegerNear b b' → IntegerNear (op a b) (op a b'))
  → Hom (IntegerGrid (suc (suc n))) (IntegerGrid (suc n))
onVertices (integerConnection i op left right) = mergeInteger i op
preserves (integerConnection {n} here op left right)
  {x = (a , b , u)} {y = (a' , b' , v)} = PT.rec (adj-isProp (IntegerGrid (suc n)) _ _) λ where
    (inl (p , e)) → PT.rec (adj-isProp (IntegerGrid (suc n)) _ _)
      (λ where
        (inl (q , e')) → ∣ inl (cong₂ op p q , e') ∣₁
        (inr (e' , q)) → ∣ inr (subst (λ z → IntegerNear (op a b) (op z b')) p
          (right a {b} {b'} e') , q) ∣₁) e
    (inr (e , p)) → ∣ inr (subst (λ z → IntegerNear (op a b) (op a' z))
      (cong fst p) (left {a} {a'} e b) , cong snd p) ∣₁
preserves (integerConnection {suc n} (there i) op left right) e =
  preserves (boxHom (idHom Iℤ) (integerConnection i op left right)) e

integerMin integerMax : {n : ℕ} → Position (suc n)
  → Hom (IntegerGrid (suc (suc n))) (IntegerGrid (suc n))
integerMin i = integerConnection i minℤ integer-min-near-left integer-min-near-right
integerMax i = integerConnection i maxℤ integer-max-near-left integer-max-near-right

clamp-merge : {n : ℕ} (k : ℕ) (i : Position (suc n))
  (opℤ : ℤ → ℤ → ℤ)
  (opF : Fin (suc (suc k)) → Fin (suc (suc k)) → Fin (suc (suc k)))
  (compatible : (a b : ℤ) → onVertices (centeredClamp k) (opℤ a b)
    ≡ opF (onVertices (centeredClamp k) a) (onVertices (centeredClamp k) b))
  (x : Vertex (IntegerGrid (suc (suc n))))
  → onVertices (centeredClampGrid k (suc n)) (mergeInteger i opℤ x)
    ≡ mergeGrid (suc k) i opF (onVertices (centeredClampGrid k (suc (suc n))) x)
clamp-merge {n} k here opℤ opF compatible (a , b , x) =
  cong (λ z → z , onVertices (centeredClampGrid k n) x) (compatible a b)
clamp-merge {suc n} k (there i) opℤ opF compatible (a , x) =
  cong (λ y → onVertices (centeredClamp k) a , y) (clamp-merge k i opℤ opF compatible x)

min-formula-on-stage : {G : Graph ℓ} {n : ℕ} (k : ℕ)
  (i : Position (suc n)) (f : Hom (Grid (suc k) (suc n)) G)
  → centeredExtend k (suc (suc n)) (f ∘g gridMin (suc k) i)
    ≡ centeredExtend k (suc n) f ∘g integerMin i
min-formula-on-stage k i f = homExt (λ x → cong (onVertices f)
  (sym (clamp-merge k i minℤ minFin (shiftedClamp-min (offset k) (suc k)) x)))

max-formula-on-stage : {G : Graph ℓ} {n : ℕ} (k : ℕ)
  (i : Position (suc n)) (f : Hom (Grid (suc k) (suc n)) G)
  → centeredExtend k (suc (suc n)) (f ∘g gridMax (suc k) i)
    ≡ centeredExtend k (suc n) f ∘g integerMax i
max-formula-on-stage k i f = homExt (λ x → cong (onVertices f)
  (sym (clamp-merge k i maxℤ maxFin (shiftedClamp-max (offset k) (suc k)) x)))

integer-min-comparison : {G : Graph ℓ} {n : ℕ} (i : Position (suc n))
  (c : Cell (N∞ G) (suc n))
  → IntegerComparison.integerHom G (suc (suc n)) (reindex (N∞ G) (cubeMin i) c)
    ≡ IntegerComparison.integerHom G (suc n) c ∘g integerMin i
integer-min-comparison {G = G} i = SQ.elimProp (λ _ → isSetGraphHom _ _)
  (λ { (k , f) → min-formula-on-stage k i f })

integer-max-comparison : {G : Graph ℓ} {n : ℕ} (i : Position (suc n))
  (c : Cell (N∞ G) (suc n))
  → IntegerComparison.integerHom G (suc (suc n)) (reindex (N∞ G) (cubeMax i) c)
    ≡ IntegerComparison.integerHom G (suc n) c ∘g integerMax i
integer-max-comparison {G = G} i = SQ.elimProp (λ _ → isSetGraphHom _ _)
  (λ { (k , f) → max-formula-on-stage k i f })

transported-min-formula : {G : Graph ℓ} {n : ℕ} (i : Position (suc n))
  (c : PaperIntegerCell G (suc n))
  → fst (reindex (transportedIntegerNerve G) (cubeMin i) c) ≡ fst c ∘g integerMin i
transported-min-formula {G = G} {n} i c =
  integer-min-comparison i (Iso.inv (colimitPaperCellIso G (suc n)) c)
  ∙ cong (λ h → h ∘g integerMin i) (cong fst (Iso.rightInv (colimitPaperCellIso G (suc n)) c))

transported-max-formula : {G : Graph ℓ} {n : ℕ} (i : Position (suc n))
  (c : PaperIntegerCell G (suc n))
  → fst (reindex (transportedIntegerNerve G) (cubeMax i) c) ≡ fst c ∘g integerMax i
transported-max-formula {G = G} {n} i c =
  integer-max-comparison i (Iso.inv (colimitPaperCellIso G (suc n)) c)
  ∙ cong (λ h → h ∘g integerMax i) (cong fst (Iso.rightInv (colimitPaperCellIso G (suc n)) c))

-- 以下直接操作的整数映射由公式给出；稳定性通过已证的运输公式
-- 转移，故没有新的存在假设。面先由独立的半直线极限定义。
directFace : {G : Graph ℓ} {n : ℕ} → Position (suc n) → Bool
  → PaperIntegerCell G (suc n) → PaperIntegerCell G n
directFace {G = G} {n} i b c = directFaceHom c i b ,
  subst (PaperStable {n = n}) (transported-face-formula c i b)
    (snd (reindex (transportedIntegerNerve G) (cubeFace i b) c))

directDegeneracy : {G : Graph ℓ} {n : ℕ} → Position (suc n)
  → PaperIntegerCell G n → PaperIntegerCell G (suc n)
directDegeneracy {G = G} {n} i c = fst c ∘g integerDelete i ,
  subst (PaperStable {n = suc n}) (transported-degeneracy-formula i c)
    (snd (reindex (transportedIntegerNerve G) (cubeDelete i) c))

directMinConnection directMaxConnection : {G : Graph ℓ} {n : ℕ} → Position (suc n)
  → PaperIntegerCell G (suc n) → PaperIntegerCell G (suc (suc n))
directMinConnection {G = G} {n} i c = fst c ∘g integerMin i ,
  subst (PaperStable {n = suc (suc n)}) (transported-min-formula i c)
    (snd (reindex (transportedIntegerNerve G) (cubeMin i) c))
directMaxConnection {G = G} {n} i c = fst c ∘g integerMax i ,
  subst (PaperStable {n = suc (suc n)}) (transported-max-formula i c)
    (snd (reindex (transportedIntegerNerve G) (cubeMax i) c))

abstract
  transported-face-direct : {G : Graph ℓ} {n : ℕ} (i : Position (suc n)) (b : Bool)
    (c : PaperIntegerCell G (suc n))
    → reindex (transportedIntegerNerve G) (cubeFace i b) c ≡ directFace i b c
  transported-face-direct i b c = Σ≡Prop (λ f → paperStable-isProp f) (transported-face-formula c i b)

  transported-degeneracy-direct : {G : Graph ℓ} {n : ℕ} (i : Position (suc n))
    (c : PaperIntegerCell G n)
    → reindex (transportedIntegerNerve G) (cubeDelete i) c ≡ directDegeneracy i c
  transported-degeneracy-direct i c = Σ≡Prop (λ f → paperStable-isProp f) (transported-degeneracy-formula i c)

  transported-min-direct : {G : Graph ℓ} {n : ℕ} (i : Position (suc n))
    (c : PaperIntegerCell G (suc n))
    → reindex (transportedIntegerNerve G) (cubeMin i) c ≡ directMinConnection i c
  transported-min-direct i c = Σ≡Prop (λ f → paperStable-isProp f) (transported-min-formula i c)

  transported-max-direct : {G : Graph ℓ} {n : ℕ} (i : Position (suc n))
    (c : PaperIntegerCell G (suc n))
    → reindex (transportedIntegerNerve G) (cubeMax i) c ≡ directMaxConnection i c
  transported-max-direct i c = Σ≡Prop (λ f → paperStable-isProp f) (transported-max-formula i c)

-- 词的计算按其语法递归：面取稳定端点，退化删坐标，connection
-- 合并相邻整数坐标；复合词从右向左作用，符合预层的反变约定。
directWordAction : {G : Graph ℓ} {m n : ℕ} → CubeWord m n
  → PaperIntegerCell G n → PaperIntegerCell G m
directWordAction {G = G} identityW c = c
directWordAction {G = G} (faceW i b) c = directFace {G = G} i b c
directWordAction {G = G} (deleteW i) c = directDegeneracy {G = G} i c
directWordAction {G = G} (minW i) c = directMinConnection {G = G} i c
directWordAction {G = G} (maxW i) c = directMaxConnection {G = G} i c
directWordAction {G = G} (composeW u v) c = directWordAction {G = G} u (directWordAction {G = G} v c)

abstract
  transported-word-direct : {G : Graph ℓ} {m n : ℕ} (w : CubeWord m n) (c : PaperIntegerCell G n)
    → reindex (transportedIntegerNerve G) (wordMap w) c ≡ directWordAction w c
  transported-word-direct {G = G} identityW c = reindex-id (transportedIntegerNerve G) c
  transported-word-direct {G = G} (faceW i b) c = transported-face-direct {G = G} i b c
  transported-word-direct {G = G} (deleteW i) c = transported-degeneracy-direct {G = G} i c
  transported-word-direct {G = G} (minW i) c = transported-min-direct {G = G} i c
  transported-word-direct {G = G} (maxW i) c = transported-max-direct {G = G} i c
  transported-word-direct {G = G} (composeW u v) c =
    cong (λ f → reindex (transportedIntegerNerve G) f c)
      (cubeMapExt {f = wordMap (composeW u v)} {g = wordMap u ⋆c wordMap v} refl)
      ∙ reindex-compose (transportedIntegerNerve G) (wordMap u) (wordMap v) c
      ∙ cong (reindex (transportedIntegerNerve G) (wordMap u)) (transported-word-direct {G = G} v c)
      ∙ transported-word-direct {G = G} u (directWordAction {G = G} v c)

-- 一个语义 cube map 只给截断的词见证。所有直接词计算都等于同一
-- 运输结果，故候选纤维为命题，可合法消去见证的截断；这不是任意
-- 选择代表词，也不假设 CubicalMap 可判定相等。
module Direct {ℓ : Level} (G : Graph ℓ) where
  ActionCandidate : {m n : ℕ} (u : CubicalMap m n) (c : PaperIntegerCell G n) → Type ℓ
  ActionCandidate {m} u c = Σ[ d ∈ PaperIntegerCell G m ]
    d ≡ reindex (transportedIntegerNerve G) u c

  -- 命题纤维的存在及唯一性已由直接词公式证明。把它们设为不透明，
  -- 只控制后续类型检查的证明归约；上面的整数坐标算法仍可直接计算。
  abstract
    actionCandidate-isProp : {m n : ℕ} (u : CubicalMap m n) (c : PaperIntegerCell G n)
      → isProp (ActionCandidate {m = m} {n = n} u c)
    actionCandidate-isProp {m} {n} u c (d , p) (e , q) =
      Σ≡Prop (λ _ → paperIntegerCell-isSet G m _ _) (p ∙ sym q)

    actionCandidate : {m n : ℕ} (u : CubicalMap m n) (c : PaperIntegerCell G n)
      → ActionCandidate {m = m} {n = n} u c
    actionCandidate {m} {n} u c = PT.rec
      {A = Σ[ w ∈ CubeWord m n ] evaluate w ≡ underlying u}
      {P = ActionCandidate {m = m} {n = n} u c}
      (actionCandidate-isProp {m = m} {n = n} u c)
      (λ { (w , p) → directWordAction {G = G} {m = m} {n = n} w c ,
        sym (transported-word-direct {G = G} {m = m} {n = n} w c)
        ∙ cong (λ (f : CubicalMap m n) → reindex (transportedIntegerNerve G) f c)
          (cubeMapExt {m = m} {n = n} {f = wordMap w} {g = u} p) })
      (generated u)

  directIntegerAction : {m n : ℕ} → CubicalMap m n → PaperIntegerCell G n → PaperIntegerCell G m
  directIntegerAction {m} {n} u c = fst (actionCandidate {m = m} {n = n} u c)

  direct-action-comparison : {m n : ℕ} (u : CubicalMap m n) (c : PaperIntegerCell G n)
    → directIntegerAction u c ≡ reindex (transportedIntegerNerve G) u c
  direct-action-comparison {m} {n} u c = snd (actionCandidate {m = m} {n = n} u c)

  directIntegerNerve : CubicalSet ℓ
  cells directIntegerNerve n = PaperIntegerCell G n , paperIntegerCell-isSet G n
  reindex directIntegerNerve = directIntegerAction
  reindex-id directIntegerNerve {n} c = direct-action-comparison (cubeId n) c
    ∙ reindex-id (transportedIntegerNerve G) c
  reindex-compose directIntegerNerve u v c = direct-action-comparison (u ⋆c v) c
    ∙ reindex-compose (transportedIntegerNerve G) u v c
    ∙ sym (cong (reindex (transportedIntegerNerve G) u) (direct-action-comparison v c))
    ∙ sym (direct-action-comparison u (directIntegerAction v c))

  -- 这些式子同时证明每个生成算子的原文直接公式及全部复合相容。
  direct-word-formula : {m n : ℕ} (w : CubeWord m n) (c : PaperIntegerCell G n)
    → reindex directIntegerNerve (wordMap w) c ≡ directWordAction w c
  direct-word-formula w c = direct-action-comparison (wordMap w) c ∙ transported-word-direct w c

  directToTransported : CubicalNatural directIntegerNerve (transportedIntegerNerve G)
  mapCells directToTransported n c = c
  natural directToTransported = direct-action-comparison

  transportedToDirect : CubicalNatural (transportedIntegerNerve G) directIntegerNerve
  mapCells transportedToDirect n c = c
  natural transportedToDirect u c = sym (direct-action-comparison u c)

open Direct public using
  (directIntegerNerve; directIntegerAction; direct-action-comparison; direct-word-formula;
   directToTransported; transportedToDirect)

integerNerveComparison : (G : Graph ℓ) → CubicalNatural (N∞ G) (directIntegerNerve G)
integerNerveComparison G = toInteger G ⋆n transportedToDirect G

integerNerveComparisonInverse : (G : Graph ℓ) → CubicalNatural (directIntegerNerve G) (N∞ G)
integerNerveComparisonInverse G = directToTransported G ⋆n fromInteger G

integerNerveComparison-left : (G : Graph ℓ)
  → integerNerveComparison G ⋆n integerNerveComparisonInverse G ≡ cubicalId (N∞ G)
integerNerveComparison-left G = cubicalNaturalExt
  {A = N∞ G} {B = N∞ G}
  {f = integerNerveComparison G ⋆n integerNerveComparisonInverse G}
  {g = cubicalId (N∞ G)}
  (λ n c → Iso.leftInv (colimitPaperCellIso G n) c)

integerNerveComparison-right : (G : Graph ℓ)
  → integerNerveComparisonInverse G ⋆n integerNerveComparison G ≡ cubicalId (directIntegerNerve G)
integerNerveComparison-right G = cubicalNaturalExt
  {A = directIntegerNerve G} {B = directIntegerNerve G}
  {f = integerNerveComparisonInverse G ⋆n integerNerveComparison G}
  {g = cubicalId (directIntegerNerve G)}
  (λ n c → Iso.rightInv (colimitPaperCellIso G n) c)

directIntegerGraphMap : {G : Graph ℓ} {H : Graph ℓ'} (h : Hom G H)
  → CubicalNatural (directIntegerNerve G) (directIntegerNerve H)
mapCells (directIntegerGraphMap h) = paperIntegerMap h
natural (directIntegerGraphMap {G = G} {H = H} h) {m} {n} u c =
  cong (paperIntegerMap h m) (direct-action-comparison G u c)
  ∙ sym (transportedGraphMap-formula h m (reindex (transportedIntegerNerve G) u c))
  ∙ natural (transportedGraphMap h) u c
  ∙ cong (reindex (transportedIntegerNerve H) u) (transportedGraphMap-formula h n c)
  ∙ sym (direct-action-comparison H u (paperIntegerMap h n c))

integerNerveComparison-graph-natural : {G : Graph ℓ} {H : Graph ℓ'} (h : Hom G H)
  → integerNerveComparison G ⋆n directIntegerGraphMap h ≡ N∞-map h ⋆n integerNerveComparison H
integerNerveComparison-graph-natural {G = G} {H = H} h = cubicalNaturalExt
  {A = N∞ G} {B = directIntegerNerve H}
  {f = integerNerveComparison G ⋆n directIntegerGraphMap h}
  {g = N∞-map h ⋆n integerNerveComparison H}
  (λ n c → sym (colimitPaperCell-natural h n c))
