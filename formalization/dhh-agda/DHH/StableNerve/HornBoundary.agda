{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.FinData using (Fin; toℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.CubeCategory
open import DHH.Cubes using (Position; here; there)
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.StableNerve.Interval using (endpoint)
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Grid
open import DHH.StableNerve.GridFaces
open import DHH.StableNerve.GridFocus
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Padding
open import DHH.StableNerve.HornDistance using (windowCoordinate)
open import DHH.StableNerve.HornWindow
open import DHH.StableNerve.HornGridDistance using (coordinateAt)
open import DHH.StableNerve.HornFocusedMap
open import DHH.StableNerve.HornFocusedBoundary
open import DHH.StableNerve.HornFaceEvaluation
open import DHH.StableNerve.HornRetraction

-- 面生成的子预层上的两映射只要在所有生成面相同便相同。
-- Contains 的截断只向 cell 集合的等式消去，覆盖全部重索引。
selected-map-ext : {ℓ : Level} {n : ℕ} (S : FaceSelection n) (A : CubicalSet ℓ)
  (f g : CubicalNatural (SelectedFaces.complex S) A)
  → ((j : Facet n) (p : fst (S j))
      → SelectedFaces.face S j p ⋆n f ≡ SelectedFaces.face S j p ⋆n g)
  → f ≡ g
selected-map-ext S A f g same = cubicalNaturalExt λ d (u , p) → PT.elim
  {P = λ q → mapCells f d (u , q) ≡ mapCells g d (u , q)}
  (λ q → snd (cells A d) _ _)
  (λ { (j , selected , v , e) →
    let change = Σ≡Prop (λ _ → squash₁)
          {u = mapCells (SelectedFaces.face S j selected) d v}
          {v = u , ∣ j , selected , v , e ∣₁} e
    in sym (cong (mapCells f d) change)
      ∙ cong (λ h → mapCells h d v) (same j selected)
      ∙ cong (mapCells g d) change }) p

-- 窗口压缩与“把一个坐标移到首位”相容。证明只沿位置递归，
-- 没有把坐标置换冒充为原 BOX 范畴中的新增生成算子。
window-insert-value : (a b r : ℕ) {n : ℕ} (i : Position (suc n))
  (v : Fin (suc r)) (x : Vertex (Grid r n))
  → onVertices (windowGrid a b r (suc n)) (insertValue r i v x)
    ≡ insertValue b i (windowCoordinate a b (toℕ v))
      (onVertices (windowGrid a b r n) x)
window-insert-value a b r here v x = refl
window-insert-value a b r {suc n} (there i) v (w , x) =
  cong (λ y → windowCoordinate a b (toℕ w) , y)
    (window-insert-value a b r i v x)

window-unfocus-focus : (a b r : ℕ) {n : ℕ} (i : Position (suc n))
  (x : Vertex (Grid r (suc n)))
  → onVertices (unfocusMap b i)
      (onVertices (windowGrid a b r (suc n)) (onVertices (focusMap r i) x))
    ≡ onVertices (windowGrid a b r (suc n)) x
window-unfocus-focus a b r {n} i x =
  sym (window-insert-value a b r i (readGridCoordinate r i x) (deleteGrid r i x))
  ∙ cong (onVertices (windowGrid a b r (suc n))) (insertValueReadDelete r i x)

-- 把任意原位置的已选外端面送到 focused 坐标的同一个外端面。
-- classifyPosition 同时覆盖特殊坐标与剩余坐标，零维也不例外。
focused-source-selected : (r n : ℕ) (i : Position (suc n)) (ε : Bool)
  (x : Vertex (Grid r (suc n))) (j : Facet n)
  → fst (exceptFace (i , ε) j)
  → readGridCoordinate r (fst j) x ≡ endpoint r (snd j)
  → SelectedPoint r ε n (onVertices (focusMap r i) x)
focused-source-selected r n i ε x (j , b) excluded outer with classifyPosition i j
... | inl same = (here , b) ,
  (λ e → excluded (cong₂ _,_ same (cong snd e))) ,
  (cong (λ t → readGridCoordinate r t x) (sym same) ∙ outer)
... | inr (k , same) = (there k , b) , other-selected {n = n} k b ε ,
  (sym (readGridCoordinate-coordinateAt r k (deleteGrid r i x))
    ∙ readDeleteSkipped r i k x
    ∙ cong (λ t → readGridCoordinate r t x) (sym same) ∙ outer)

module BoundaryProof (r n : ℕ) (missing : Facet n) where
  module R = Retraction r n missing
  open R using (m; i; ε; environment)
  width : ℕ
  width = m + (m + m)

  environment-on-selected : (x : Vertex (Grid width (suc n)))
    (j : Facet n) → fst (exceptFace missing j)
    → readGridCoordinate width (fst j) x ≡ endpoint width (snd j)
    → onVertices environment x ≡ onVertices (windowGrid m m width (suc n)) x
  environment-on-selected x j excluded outer =
    cong (onVertices (unfocusMap m i))
      (value-on-selected m ε n (onVertices (focusMap width i) x)
        (fst witness) (fst (snd witness)) (snd (snd witness)))
    ∙ window-unfocus-focus m m width i x
    where
    witness = focused-source-selected width n i ε x j excluded outer

  environment-face : (j : Facet n) (excluded : fst (exceptFace missing j))
    (x : Vertex (Grid width n))
    → onVertices environment (insertGrid width (fst j) (snd j) x)
      ≡ insertGrid m (fst j) (snd j) (onVertices (middleGrid m n) x)
  environment-face j excluded x =
    environment-on-selected (insertGrid width (fst j) (snd j) x) j excluded
      (grid-read-insert width (fst j) (snd j) x)
    ∙ sym (middle-grid-value m (suc n) (insertGrid width (fst j) (snd j) x))
    ∙ map-insert (middleCollapse m) (fst j) (snd j) x

  -- 评价与选面选择无关，故收缩输出无论使用哪张面作证书，
  -- 在已有面上都恢复 η 对窗口压缩后的原面点的评价。
  module TargetBoundary {ℓ : Level} (H : Graph ℓ)
    (η : CubicalNatural (OpenBox missing) (Nₘ m H)) where
    module T = R.Target H η

    face-value : (j : Facet n) (excluded : fst (exceptFace missing j))
      (x : Vertex (Grid width n))
      → onVertices T.map (insertGrid width (fst j) (snd j) x)
        ≡ onVertices (E m (exceptFace missing) η j excluded)
          (onVertices (middleGrid m n) x)
    face-value j excluded x = T.V.agrees
      (onVertices environment (insertGrid width (fst j) (snd j) x))
      (T.points (insertGrid width (fst j) (snd j) x)) j excluded
      (onVertices (middleGrid m n) x) (sym (environment-face j excluded x))

    face-map : (j : Facet n) (excluded : fst (exceptFace missing j))
      → T.map ∘g gridFace width (fst j) (snd j)
        ≡ E m (exceptFace missing) η j excluded ∘g middleGrid m n
    face-map j excluded = homExt (face-value j excluded)

    filled : CubicalNatural (OpenBox missing) (Nₘ width H)
    filled = openBoxInclusion missing ⋆n classifyCube (Nₘ width H) T.map

    refined : CubicalNatural (OpenBox missing) (Nₘ width H)
    refined = η ⋆n changeSize (middleCollapse m) H

    face-generator : (j : Facet n) (excluded : fst (exceptFace missing j))
      → mapCells (SelectedFaces.face (exceptFace missing) j excluded ⋆n filled) n (cubeId n)
        ≡ mapCells (SelectedFaces.face (exceptFace missing) j excluded ⋆n refined) n (cubeId n)
    face-generator j excluded =
      cong (λ u → T.map ∘g gridAction width u)
        (Category.⋆IdL CubeCategory (facetMap j))
      ∙ face-map j excluded

    full-boundary : filled ≡ refined
    full-boundary = selected-map-ext (exceptFace missing) (Nₘ width H) filled refined
      (λ j p → sym (every-natural-classified (Nₘ width H)
        (SelectedFaces.face (exceptFace missing) j p ⋆n filled))
        ∙ cong (classifyCube (Nₘ width H)) (face-generator j p)
        ∙ every-natural-classified (Nₘ width H)
          (SelectedFaces.face (exceptFace missing) j p ⋆n refined))

-- full-boundary 是整个 horn 子预层的自然变换等式，含所有维数、
-- 面、退化及 connection 的重索引。稳定阶段比较在 StagePadding。
