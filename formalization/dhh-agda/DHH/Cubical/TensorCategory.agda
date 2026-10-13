{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.TensorCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.Cubes using (Q)
open import DHH.CubeCategory
open import DHH.Cubical.TensorCategory.Coordinates
open import DHH.Cubical.TensorCategory.Words

-- 分块张量的图映射已经具体给出；有限词闭包证明它仍是立方态射。
-- 生成性是命题，故从两个截断词证书作 PT.rec2 合法，不需选代表元。
infixr 25 _⊗c_
_⊗c_ : {m n p q : ℕ} → CubicalMap m n → CubicalMap p q → CubicalMap (m + p) (n + q)
underlying (_⊗c_ {m} {n} {p} {q} f g) = tensorHom {m} {n} {p} {q} (underlying f) (underlying g)
generated (_⊗c_ {m} {n} {p} {q} f g) = PT.rec2 squash₁
  (λ { (u , e) (v , d) → ∣ tensorWord u v ,
    (tensor-evaluate u v ∙ cong₂ (tensorHom {m} {n} {p} {q}) e d) ∣₁ })
  (generated f) (generated g)

tensor-on-append : {m n p q : ℕ} (f : CubicalMap m n) (g : CubicalMap p q)
  (x : Vertex (Q m)) (y : Vertex (Q p))
  → onVertices (underlying (f ⊗c g)) (appendPoint m p x y)
    ≡ appendPoint n q (onVertices (underlying f) x) (onVertices (underlying g) y)
tensor-on-append {m} {n} {p} {q} f g = tensorHom-on-append {m} {n} {p} {q} (underlying f) (underlying g)

tensor-id : (m p : ℕ) → cubeId m ⊗c cubeId p ≡ cubeId (m + p)
tensor-id m p = cubeMapExt (tensorHom-id m p)

tensor-compose : {m n k p q r : ℕ}
  (f : CubicalMap m n) (f' : CubicalMap n k)
  (g : CubicalMap p q) (g' : CubicalMap q r)
  → (f ⋆c f') ⊗c (g ⋆c g') ≡ (f ⊗c g) ⋆c (f' ⊗c g')
tensor-compose {m} {n} {k} {p} {q} {r} f f' g g' = cubeMapExt
  (tensorHom-compose {m} {n} {k} {p} {q} {r} (underlying f) (underlying f') (underlying g) (underlying g'))

tensor-word : {m n p q : ℕ} (f : CubeWord m n) (g : CubeWord p q)
  → wordMap (tensorWord f g) ≡ wordMap f ⊗c wordMap g
tensor-word f g = cubeMapExt (tensor-evaluate f g)

-- 本模块给出对象上的加法及态射张量的单位/复合函子律。
-- 预层的 Day tensor、其结合/单位相容图以及稳定神经的 lax 结构，
-- 仍是进一步的构造，不由这个闭包定理自动获得。
