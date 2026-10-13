{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.ExponentialFunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import DHH.Simplicial.Sets
open import DHH.Simplicial.Products
open import DHH.Simplicial.Exponentials
open import DHH.Simplicial.FullSubcomplex
open import DHH.Simplicial.Marked

private variable ℓX ℓY ℓZ ℓQ : Level

-- 固定 f:X→Y，参数族 Δ[n]×Y→Q 通过 id×f 拉回。
-- 每一步操作只作已有自然变换的复合，不枚举全部参数族。
precomposeExponential : {X : SimplicialSet ℓX} {Y : SimplicialSet ℓY}
  (f : SimplicialNatural X Y) (Q : SimplicialSet ℓQ)
  → SimplicialNatural (ExponentialS Y Q) (ExponentialS X Q)
mapS (precomposeExponential {X = X} {Y = Y} f Q) n h =
  productSMap {A = RepresentableSimplex n} {B = RepresentableSimplex n} {C = X} {D = Y}
    (simplicialId (RepresentableSimplex n)) f ⋆s h
naturalS (precomposeExponential f Q) u h = simplicialNaturalExt (λ m c → refl)

precomposeExponential-id : (X : SimplicialSet ℓX) (Q : SimplicialSet ℓQ)
  → precomposeExponential (simplicialId X) Q ≡ simplicialId (ExponentialS X Q)
precomposeExponential-id X Q = simplicialNaturalExt (λ n h → simplicialNaturalExt (λ m c → refl))

precomposeExponential-compose : {X : SimplicialSet ℓX} {Y : SimplicialSet ℓY} {Z : SimplicialSet ℓZ}
  (f : SimplicialNatural X Y) (g : SimplicialNatural Y Z) (Q : SimplicialSet ℓQ)
  → precomposeExponential (f ⋆s g) Q ≡ precomposeExponential g Q ⋆s precomposeExponential f Q
precomposeExponential-compose f g Q = simplicialNaturalExt (λ n h → simplicialNaturalExt (λ m c → refl))

zeroFunctor-precompose : {X : SimplicialSet ℓX} {Y : SimplicialSet ℓY}
  (f : SimplicialNatural X Y) (Q : SimplicialSet ℓQ) (h : SCell (ExponentialS Y Q) 0)
  → zeroFunctor X (mapS (precomposeExponential f Q) 0 h) ≡ f ⋆s zeroFunctor Y h
zeroFunctor-precompose f Q h = simplicialNaturalExt (λ n a → refl)

-- 参数单形的第 i 个顶点给出一个实际函子 Y→Q；预合成后得到的
-- X→Q 正是该函子与 f 的复合。这是 restriction 保标记的关键等式。
vertexFunctor-precompose : {X : SimplicialSet ℓX} {Y : SimplicialSet ℓY}
  (f : SimplicialNatural X Y) (Q : SimplicialSet ℓQ) {n : ℕ}
  (h : SCell (ExponentialS Y Q) n) (i : Fin (suc n))
  → zeroFunctor X (vertexOf (ExponentialS X Q) (mapS (precomposeExponential f Q) n h) i)
    ≡ f ⋆s zeroFunctor Y (vertexOf (ExponentialS Y Q) h i)
vertexFunctor-precompose {X = X} {Y = Y} f Q h i =
  sym (cong (zeroFunctor X) (naturalS (precomposeExponential f Q) (vertexOrdinal i) h))
  ∙ zeroFunctor-precompose f Q (vertexOf (ExponentialS Y Q) h i)
