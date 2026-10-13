{-# OPTIONS --cubical --safe #-}

module DHH.StableNerve.GridFocus where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Bool using (Bool; false; true; false≢true; true≢false)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.Cubes using (Position; here; there)
open import DHH.StableNerve.Interval using (Iₘ; endpoint)
open import DHH.StableNerve.Grid
open import DHH.StableNerve.GridFaces using (readGridCoordinate)
open import DHH.StableNerve.HornGridDistance using (coordinateAt)

-- 插入任意区间值，而非仅插入端点。位置的 there 分支保留头坐标，
-- 在余下坐标中递归；因而适用于任意宽度（包括零）和任意维数。
insertValue : (r : ℕ) {n : ℕ} → Position (suc n)
  → Fin (suc r) → Vertex (Grid r n) → Vertex (Grid r (suc n))
insertValue r here a x = a , x
insertValue r {suc n} (there i) a (b , x) = b , insertValue r i a x

readInsertValue : (r : ℕ) {n : ℕ} (i : Position (suc n))
  (a : Fin (suc r)) (x : Vertex (Grid r n))
  → readGridCoordinate r i (insertValue r i a x) ≡ a
readInsertValue r here a x = refl
readInsertValue r {suc n} (there i) a (b , x) = readInsertValue r i a x

deleteInsertValue : (r : ℕ) {n : ℕ} (i : Position (suc n))
  (a : Fin (suc r)) (x : Vertex (Grid r n))
  → deleteGrid r i (insertValue r i a x) ≡ x
deleteInsertValue r here a x = refl
deleteInsertValue r {suc n} (there i) a (b , x) =
  cong (λ y → b , y) (deleteInsertValue r i a x)

insertValueReadDelete : (r : ℕ) {n : ℕ} (i : Position (suc n))
  (x : Vertex (Grid r (suc n)))
  → insertValue r i (readGridCoordinate r i x) (deleteGrid r i x) ≡ x
insertValueReadDelete r here (a , x) = refl
insertValueReadDelete r {suc n} (there i) (a , x) =
  cong (λ y → a , y) (insertValueReadDelete r i x)

insertValue-endpoint : (r : ℕ) {n : ℕ} (i : Position (suc n))
  (b : Bool) (x : Vertex (Grid r n))
  → insertValue r i (endpoint r b) x ≡ insertGrid r i b x
insertValue-endpoint r here b x = refl
insertValue-endpoint r {suc n} (there i) b (a , x) =
  cong (λ y → a , y) (insertValue-endpoint r i b x)

-- 把指定坐标移到首位，其余坐标按原顺序保留。保边证明逐层消去
-- BOX 的截断分支：原头坐标变化时，变化转入输出的第二块；尾部
-- 变化时，递归区分被读取坐标变化或剩余网格变化。
focusMap : (r : ℕ) {n : ℕ} (i : Position (suc n))
  → Hom (Grid r (suc n)) (Iₘ r BOX Grid r n)
onVertices (focusMap r i) x = readGridCoordinate r i x , deleteGrid r i x
preserves (focusMap r here) e = e
preserves (focusMap r {suc n} (there i)) {x = a , x} {y = b , y} =
  PT.rec squash₁ λ where
    (inl (p , e)) → PT.rec squash₁
      (λ where
        (inl (q , f)) → ∣ inl (q , ∣ inl (p , f) ∣₁) ∣₁
        (inr (f , q)) → ∣ inr (f , cong₂ _,_ p q) ∣₁)
      (preserves (focusMap r i) e)
    (inr (e , p)) → ∣ inl (cong (readGridCoordinate r i) p ,
      ∣ inr (e , cong (deleteGrid r i) p) ∣₁) ∣₁

-- 逆映射也独立证明保边。被插入的坐标变化时只在递归插入处产生
-- 一条边；保留的头坐标变化时，所有插入后的尾坐标保持相等。
-- 这里没有从顶点双射推断图同构。
unfocusMap : (r : ℕ) {n : ℕ} (i : Position (suc n))
  → Hom (Iₘ r BOX Grid r n) (Grid r (suc n))
onVertices (unfocusMap r i) (a , x) = insertValue r i a x
preserves (unfocusMap r here) e = e
preserves (unfocusMap r {suc n} (there i)) {x = a , b , x} {y = a' , b' , y} =
  PT.rec squash₁ λ where
    (inl (p , e)) → PT.rec squash₁
      (λ where
        (inl (q , f)) → ∣ inl (q , preserves (unfocusMap r i) ∣ inl (p , f) ∣₁) ∣₁
        (inr (f , q)) → ∣ inr (f , cong₂ (insertValue r i) p q) ∣₁) e
    (inr (e , p)) → ∣ inl (cong fst p ,
      preserves (unfocusMap r i) ∣ inr (e , cong snd p) ∣₁) ∣₁

-- 两个互逆等式是完整 Hom 的等式；顶点递归恒等式经 homExt 提升，
-- 邻接的命题性保证已经构造的保边证明也相容。
focus-unfocus : (r : ℕ) {n : ℕ} (i : Position (suc n))
  → focusMap r i ∘g unfocusMap r i ≡ idHom (Iₘ r BOX Grid r n)
focus-unfocus r i = homExt λ { (a , x) →
  cong₂ _,_ (readInsertValue r i a x) (deleteInsertValue r i a x) }

unfocus-focus : (r : ℕ) {n : ℕ} (i : Position (suc n))
  → unfocusMap r i ∘g focusMap r i ≡ idHom (Grid r (suc n))
unfocus-focus r i = homExt (insertValueReadDelete r i)

-- 与距离和模块的坐标算法识别；后续可以直接把端面证书运输到
-- focus 的首坐标，无需更改任一模块的坐标表示。
readGridCoordinate-coordinateAt : (r : ℕ) {n : ℕ} (i : Position n)
  (x : Vertex (Grid r n)) → readGridCoordinate r i x ≡ coordinateAt r i x
readGridCoordinate-coordinateAt r here (a , x) = refl
readGridCoordinate-coordinateAt r (there i) (a , x) = readGridCoordinate-coordinateAt r i x

-- 删除第 i 个坐标后，剩余位置 j 在原网格中的位置。遇到被跳过的
-- 首位整体后移；其余情形保留共同前缀，故无需算术编码或枚举。
skipPosition : {n : ℕ} → Position (suc n) → Position n → Position (suc n)
skipPosition here j = there j
skipPosition {suc n} (there i) here = here
skipPosition {suc n} (there i) (there j) = there (skipPosition i j)

private
  firstPosition : {n : ℕ} → Position (suc n) → Bool
  firstPosition here = true
  firstPosition (there i) = false

  tailPosition : {n : ℕ} → Position (suc (suc n)) → Position (suc n)
  tailPosition here = here
  tailPosition (there i) = i

skipPosition-distinct : {n : ℕ} (i : Position (suc n)) (j : Position n)
  → skipPosition i j ≡ i → ⊥
skipPosition-distinct here j e = false≢true (cong firstPosition e)
skipPosition-distinct {suc n} (there i) here e = true≢false (cong firstPosition e)
skipPosition-distinct {suc n} (there i) (there j) e =
  skipPosition-distinct i j (cong tailPosition e)

-- 每个环境坐标要么是被提到首位的坐标，要么位于剩余坐标
-- 列表的某处。此处输出需要的定位见证，不依赖排中律或有限搜索。
classifyPosition : {n : ℕ} (i j : Position (suc n))
  → (j ≡ i) ⊎ (Σ[ k ∈ Position n ] j ≡ skipPosition i k)
classifyPosition here here = inl refl
classifyPosition here (there j) = inr (j , refl)
classifyPosition {suc n} (there i) here = inr (here , refl)
classifyPosition {suc n} (there i) (there j) with classifyPosition i j
... | inl e = inl (cong there e)
... | inr (k , e) = inr (there k , cong there e)

-- 插入任意新值不会改变其余坐标；这个等式把 focused 网格中的
-- 共同端面证书运送到原位置 skipPosition i j。
readSkippedInsertValue : (r : ℕ) {n : ℕ}
  (i : Position (suc n)) (j : Position n) (a : Fin (suc r))
  (x : Vertex (Grid r n))
  → readGridCoordinate r (skipPosition i j) (insertValue r i a x)
    ≡ readGridCoordinate r j x
readSkippedInsertValue r here j a x = refl
readSkippedInsertValue r {suc n} (there i) here a (b , x) = refl
readSkippedInsertValue r {suc n} (there i) (there j) a (b , x) =
  readSkippedInsertValue r i j a x

readDeleteSkipped : (r : ℕ) {n : ℕ}
  (i : Position (suc n)) (j : Position n) (x : Vertex (Grid r (suc n)))
  → readGridCoordinate r j (deleteGrid r i x)
    ≡ readGridCoordinate r (skipPosition i j) x
readDeleteSkipped r i j x =
  sym (readSkippedInsertValue r i j (readGridCoordinate r i x) (deleteGrid r i x))
  ∙ cong (readGridCoordinate r (skipPosition i j)) (insertValueReadDelete r i x)
