{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornRetraction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; _+_)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.Cubes using (Position; here; there)
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.Cubical.GraphCoend
open import DHH.StableNerve.Interval using (endpoint)
open import DHH.StableNerve.Grid
open import DHH.StableNerve.GridFaces
open import DHH.StableNerve.GridFocus
open import DHH.StableNerve.Nerve using (Nₘ)
open import DHH.StableNerve.HornGridDistance using (coordinateAt)
open import DHH.StableNerve.HornFocusedMap
open import DHH.StableNerve.HornSelectedEvaluation

-- 把首坐标的选面证书搬回原位置。skipPosition 由删除坐标的
-- 递归定义给出，所以任意缺面位置均覆盖，不限于二维/三维。
moveFacet : {n : ℕ} → Position (suc n) → Facet n → Facet n
moveFacet i (here , b) = i , b
moveFacet i (there j , b) = skipPosition i j , b

move-direction : {n : ℕ} (i : Position (suc n)) (j : Facet n)
  → snd (moveFacet i j) ≡ snd j
move-direction i (here , b) = refl
move-direction i (there j , b) = refl

move-selected : {n : ℕ} (i : Position (suc n)) (ε : Bool)
  (j : Facet n) → fst (exceptFace (here , ε) j)
  → fst (exceptFace (i , ε) (moveFacet i j))
move-selected i ε (here , b) p e = p (cong (λ a → here , a) (cong snd e))
move-selected i ε (there j , b) p e = skipPosition-distinct i j (cong fst e)

move-coordinate : (m : ℕ) {n : ℕ} (i : Position (suc n)) (j : Facet n)
  (a : Fin (suc m)) (x : Vertex (Grid m n))
  → readGridCoordinate m (fst (moveFacet i j)) (insertValue m i a x)
    ≡ coordinateAt m (fst j) (a , x)
move-coordinate m i (here , b) a x = readInsertValue m i a x
move-coordinate m i (there j , b) a x = readSkippedInsertValue m i j a x
  ∙ readGridCoordinate-coordinateAt m j x

module Retraction (r n : ℕ) (missing : Facet n) where
  m : ℕ
  m = suc r
  R : ℕ
  R = m + (m + m)

  i : Position (suc n)
  i = fst missing
  ε : Bool
  ε = snd missing

  module F = Focused m ε n

  -- 先把特殊坐标提到首位，运行经过保边检查的收缩，再恢复位置。
  environment : Hom (Grid R (suc n)) (Grid m (suc n))
  environment = unfocusMap m i ∘g (F.map ∘g focusMap R i)

  module Target {ℓ : Level} (H : Graph ℓ)
    (η : CubicalNatural (OpenBox missing) (Nₘ m H)) where
    module V = Evaluate r n H (exceptFace missing) η

    points : (x : Vertex (Grid R (suc n))) → V.PointWitness (onVertices environment x)
    points x = convert (F.selected-point (onVertices (focusMap R i) x))
      where
      y = F.value (onVertices (focusMap R i) x)
      convert : SelectedPoint m ε n y → V.PointWitness (onVertices environment x)
      convert (j , p , q) = moveFacet i j , move-selected i ε j p ,
        move-coordinate m i j (fst y) (snd y) ∙ q ∙ cong (endpoint m) (sym (move-direction i j))

    shared : {x y : Vertex (Grid R (suc n))} → Adj (Grid R (suc n)) x y
      → ∥ V.SharedWitness (onVertices environment x) (onVertices environment y) ∥₁
    shared {x} {y} e = PT.map convert
      (F.shared-face (preserves (focusMap R i) e))
      where
      x' = F.value (onVertices (focusMap R i) x)
      y' = F.value (onVertices (focusMap R i) y)
      convert : SharedSelectedFace m ε n x' y'
        → V.SharedWitness (onVertices environment x) (onVertices environment y)
      convert (j , p , q , s) = moveFacet i j , move-selected i ε j p ,
        (move-coordinate m i j (fst x') (snd x') ∙ q ∙ cong (endpoint m) (sym (move-direction i j))) ,
        (move-coordinate m i j (fst y') (snd y') ∙ s ∙ cong (endpoint m) (sym (move-direction i j)))

    map : Hom (Grid R (suc n)) H
    map = V.liftMap environment points shared

  -- 目标是实际 Γ_m(horn)。其边仍由同一个生成面见证；上面的
  -- liftMap 没有采用环境诱导子图或边的传递闭包。
  graph : Graph ℓ-zero
  graph = Γₘ m (OpenBox missing)

  contraction : Hom (Grid R (suc n)) graph
  contraction = Target.map graph (GraphCoend.unit m (OpenBox missing))

-- contraction 已实际构造且保边。逐面边界和指定 stage 过渡的
-- 识别是独立接口；未支付它们前不能当作 Universal.Fill。
