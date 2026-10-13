{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornSelectedEvaluation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.StableNerve.Interval using (endpoint)
open import DHH.StableNerve.Grid
open import DHH.StableNerve.GridFaces
open import DHH.StableNerve.Nerve using (Nₘ)
open import DHH.StableNerve.HornFaceEvaluation

-- 只在已经给出选面证书的点上评价。没有为图余端的商点选代表，
-- 也没有把选面顶点的环境诱导子图误当成按面生成的图。
module Evaluate {ℓ : Level} (r n : ℕ) (H : Graph ℓ)
  (S : FaceSelection n)
  (η : CubicalNatural (SelectedFaces.complex S) (Nₘ (suc r) H)) where

  m : ℕ
  m = suc r

  PointWitness : Vertex (Grid m (suc n)) → Type₀
  PointWitness x = Σ[ j ∈ Facet n ]
    (fst (S j) × (readGridCoordinate m (fst j) x ≡ endpoint m (snd j)))

  SharedWitness : Vertex (Grid m (suc n)) → Vertex (Grid m (suc n)) → Type₀
  SharedWitness x y = Σ[ j ∈ Facet n ]
    (fst (S j) × (readGridCoordinate m (fst j) x ≡ endpoint m (snd j))
      × (readGridCoordinate m (fst j) y ≡ endpoint m (snd j)))

  value : (x : Vertex (Grid m (suc n))) → PointWitness x → Vertex H
  value x (j , p , e) = onVertices (E m S η j p) (deleteGrid m (fst j) x)

  -- 任意选择都与任意另一张生成面的评价一致。正长度排除了同一
  -- 坐标的相反端点相等；不同坐标使用实际余维二面因子化。
  agrees : (x : Vertex (Grid m (suc n))) (w : PointWitness x)
    (j : Facet n) (p : fst (S j)) (y : Vertex (Grid m n))
    → insertGrid m (fst j) (snd j) y ≡ x
    → value x w ≡ onVertices (E m S η j p) y
  agrees x (k , q , e) j p y f = face-point-evaluation r S η k j q p
    (deleteGrid m (fst k) x) y
    (grid-insert-delete-on-face m (fst k) (snd k) x e ∙ sym f)

  independent : (x : Vertex (Grid m (suc n))) (v w : PointWitness x)
    → value x v ≡ value x w
  independent x v (j , p , e) = agrees x v j p (deleteGrid m (fst j) x)
    (grid-insert-delete-on-face m (fst j) (snd j) x e)

  edge : {x y : Vertex (Grid m (suc n))}
    (v : PointWitness x) (w : PointWitness y)
    → Adj (Grid m (suc n)) x y → SharedWitness x y
    → Adj H (value x v) (value y w)
  edge {x} {y} v w e (j , p , qx , qy) =
    subst2 (Adj H)
      (sym (agrees x v j p (deleteGrid m (fst j) x)
        (grid-insert-delete-on-face m (fst j) (snd j) x qx)))
      (sym (agrees y w j p (deleteGrid m (fst j) y)
        (grid-insert-delete-on-face m (fst j) (snd j) y qy)))
      (preserves (E m S η j p) (preserves (gridDelete m (fst j)) e))

  -- 共同面仅为截断存在也足够：最终消去目标是 H 的邻接命题。
  -- A、H 可在不同且任意的 universe，均无需有限或可枚举。
  liftMap : {ℓ' : Level} {A : Graph ℓ'}
    (f : Hom A (Grid m (suc n)))
    (points : (x : Vertex A) → PointWitness (onVertices f x))
    → ({x y : Vertex A} → Adj A x y
        → ∥ SharedWitness (onVertices f x) (onVertices f y) ∥₁)
    → Hom A H
  onVertices (liftMap f points shared) x = value (onVertices f x) (points x)
  preserves (liftMap f points shared) {x} {y} e =
    PT.rec (adj-isProp H _ _) (edge (points x) (points y) (preserves f e)) (shared e)

-- 本模块把有证书的环境收缩接入任何实际选面映射。它没有提供
-- 收缩的逐面边界等式，也没有由此宣称稳定 nerve 已经是 Kan。
