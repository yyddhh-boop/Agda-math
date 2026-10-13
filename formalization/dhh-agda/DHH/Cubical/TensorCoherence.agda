{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.TensorCoherence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category; CatIso; catiso)
open import DHH.Graph
open import DHH.Cubes using (Q)
open import DHH.CubeCategory
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCategory.Coordinates

cubeTensorLeftUnit : {m n : ℕ} (f : CubicalMap m n) → cubeId zero ⊗c f ≡ f
cubeTensorLeftUnit f = cubeMapExt (homExt (λ _ → refl))

-- 右侧零维块在自然数编码中留下 n+0。逐坐标递归删去/加入空块，
-- 每步都是已生成的立方张量态射，故没有假定任意图映射都属于 □。
cubeRightUnit : (n : ℕ) → CubicalMap (n + zero) n
cubeRightUnit zero = cubeId zero
cubeRightUnit (suc n) = cubeId (suc zero) ⊗c cubeRightUnit n

cubeRightUnitInv : (n : ℕ) → CubicalMap n (n + zero)
cubeRightUnitInv zero = cubeId zero
cubeRightUnitInv (suc n) = cubeId (suc zero) ⊗c cubeRightUnitInv n

cubeRightUnit-on-append : (n : ℕ) (x : Vertex (Q n)) (u : Vertex (Q zero))
  → onVertices (underlying (cubeRightUnit n)) (appendPoint n zero x u) ≡ x
cubeRightUnit-on-append zero tt tt = refl
cubeRightUnit-on-append (suc n) (b , x) tt =
  cong (b ,_) (cubeRightUnit-on-append n x tt)

cubeRightUnitInv-on-point : (n : ℕ) (x : Vertex (Q n))
  → onVertices (underlying (cubeRightUnitInv n)) x ≡ appendPoint n zero x tt
cubeRightUnitInv-on-point zero tt = refl
cubeRightUnitInv-on-point (suc n) (b , x) =
  cong (b ,_) (cubeRightUnitInv-on-point n x)

cubeRightUnit-section : (n : ℕ) → cubeRightUnitInv n ⋆c cubeRightUnit n ≡ cubeId n
cubeRightUnit-section n = cubeMapExt (homExt λ x →
  cong (onVertices (underlying (cubeRightUnit n))) (cubeRightUnitInv-on-point n x)
  ∙ cubeRightUnit-on-append n x tt)

cubeRightUnit-retract : (n : ℕ) → cubeRightUnit n ⋆c cubeRightUnitInv n ≡ cubeId (n + zero)
cubeRightUnit-retract n = cubeMapExt
  (appendHomExt {m = n} {n = zero} {k = n + zero}
    {f = underlying (cubeRightUnit n ⋆c cubeRightUnitInv n)} {g = underlying (cubeId (n + zero))} λ x u →
    cong (onVertices (underlying (cubeRightUnitInv n))) (cubeRightUnit-on-append n x u)
    ∙ cubeRightUnitInv-on-point n x)

cubeRightUnitIso : (n : ℕ) → CatIso CubeCategory (n + zero) n
cubeRightUnitIso n = catiso (cubeRightUnit n) (cubeRightUnitInv n)
  (cubeRightUnit-section n) (cubeRightUnit-retract n)

cubeRightUnit-natural : {m n : ℕ} (f : CubicalMap m n)
  → (f ⊗c cubeId zero) ⋆c cubeRightUnit n ≡ cubeRightUnit m ⋆c f
cubeRightUnit-natural {m} {n} f = cubeMapExt
  (appendHomExt {m = m} {n = zero} {k = n}
    {f = underlying ((f ⊗c cubeId zero) ⋆c cubeRightUnit n)} {g = underlying (cubeRightUnit m ⋆c f)} λ x u →
    cong (onVertices (underlying (cubeRightUnit n))) (tensor-on-append f (cubeId zero) x u)
    ∙ cubeRightUnit-on-append n (onVertices (underlying f) x) u
    ∙ sym (cong (onVertices (underlying f)) (cubeRightUnit-on-append m x u)))

cubeRightUnitInv-natural : {m n : ℕ} (f : CubicalMap m n)
  → cubeRightUnitInv m ⋆c (f ⊗c cubeId zero) ≡ f ⋆c cubeRightUnitInv n
cubeRightUnitInv-natural {m} {n} f = cubeMapExt (homExt λ x →
  cong (onVertices (underlying (f ⊗c cubeId zero))) (cubeRightUnitInv-on-point m x)
  ∙ tensor-on-append f (cubeId zero) x tt
  ∙ sym (cubeRightUnitInv-on-point n (onVertices (underlying f) x)))

-- 任意右块 p→0 都被单位评价收起；下面逐点公式将用于 coend 的
-- 重索引关系，而不是要求唯一/规范的生成词。
rightUnit-collapse : (p q : ℕ) (v : CubicalMap q zero)
  (x : Vertex (Q p)) (y : Vertex (Q q))
  → onVertices (underlying ((cubeId p ⊗c v) ⋆c cubeRightUnit p))
      (appendPoint p q x y) ≡ x
rightUnit-collapse p q v x y =
  cong (onVertices (underlying (cubeRightUnit p))) (tensor-on-append (cubeId p) v x y)
  ∙ cubeRightUnit-on-append p x (onVertices (underlying v) y)

right-unit-chart : {p p' q q' : ℕ}
  (f : CubicalMap p p') (g : CubicalMap q q') (v : CubicalMap q' zero)
  → (((cubeId p ⊗c (g ⋆c v)) ⋆c cubeRightUnit p) ⋆c f)
    ≡ ((f ⊗c g) ⋆c ((cubeId p' ⊗c v) ⋆c cubeRightUnit p'))
right-unit-chart {p} {p'} {q} {q'} f g v = cubeMapExt
  (appendHomExt {m = p} {n = q} {k = p'}
    {f = underlying (((cubeId p ⊗c (g ⋆c v)) ⋆c cubeRightUnit p) ⋆c f)}
    {g = underlying ((f ⊗c g) ⋆c ((cubeId p' ⊗c v) ⋆c cubeRightUnit p'))} λ x y →
    cong (onVertices (underlying f)) (rightUnit-collapse p q (g ⋆c v) x y)
    ∙ sym (cong (onVertices (underlying ((cubeId p' ⊗c v) ⋆c cubeRightUnit p')))
        (tensor-on-append f g x y)
      ∙ rightUnit-collapse p' q' v (onVertices (underlying f) x) (onVertices (underlying g) y)))

-- 加法的结合重新括号也按左块 p 递归。每步保留第一个坐标；
-- p=0 时两种括号已经定义相同。这是实际态射，非未证明的接口字段。
cubeAssociator : (p q r : ℕ) → CubicalMap ((p + q) + r) (p + (q + r))
cubeAssociator zero q r = cubeId (q + r)
cubeAssociator (suc p) q r = cubeId (suc zero) ⊗c cubeAssociator p q r

cubeAssociatorInv : (p q r : ℕ) → CubicalMap (p + (q + r)) ((p + q) + r)
cubeAssociatorInv zero q r = cubeId (q + r)
cubeAssociatorInv (suc p) q r = cubeId (suc zero) ⊗c cubeAssociatorInv p q r

cubeAssociator-on-append : (p q r : ℕ)
  (x : Vertex (Q p)) (y : Vertex (Q q)) (z : Vertex (Q r))
  → onVertices (underlying (cubeAssociator p q r))
      (appendPoint (p + q) r (appendPoint p q x y) z)
    ≡ appendPoint p (q + r) x (appendPoint q r y z)
cubeAssociator-on-append zero q r tt y z = refl
cubeAssociator-on-append (suc p) q r (b , x) y z =
  cong (b ,_) (cubeAssociator-on-append p q r x y z)

cubeAssociatorInv-on-append : (p q r : ℕ)
  (x : Vertex (Q p)) (y : Vertex (Q q)) (z : Vertex (Q r))
  → onVertices (underlying (cubeAssociatorInv p q r))
      (appendPoint p (q + r) x (appendPoint q r y z))
    ≡ appendPoint (p + q) r (appendPoint p q x y) z
cubeAssociatorInv-on-append zero q r tt y z = refl
cubeAssociatorInv-on-append (suc p) q r (b , x) y z =
  cong (b ,_) (cubeAssociatorInv-on-append p q r x y z)

cubeAssociator-section : (p q r : ℕ)
  → cubeAssociatorInv p q r ⋆c cubeAssociator p q r ≡ cubeId (p + (q + r))
cubeAssociator-section zero q r = cubeMapExt (homExt (λ _ → refl))
cubeAssociator-section (suc p) q r = cubeMapExt (homExt λ { (b , x) →
  cong (b ,_) (cong (λ f → onVertices (underlying f) x) (cubeAssociator-section p q r)) })

cubeAssociator-retract : (p q r : ℕ)
  → cubeAssociator p q r ⋆c cubeAssociatorInv p q r ≡ cubeId ((p + q) + r)
cubeAssociator-retract zero q r = cubeMapExt (homExt (λ _ → refl))
cubeAssociator-retract (suc p) q r = cubeMapExt (homExt λ { (b , x) →
  cong (b ,_) (cong (λ f → onVertices (underlying f) x) (cubeAssociator-retract p q r)) })

cubeAssociatorIso : (p q r : ℕ) → CatIso CubeCategory ((p + q) + r) (p + (q + r))
cubeAssociatorIso p q r = catiso (cubeAssociator p q r) (cubeAssociatorInv p q r)
  (cubeAssociator-section p q r) (cubeAssociator-retract p q r)

-- 任意三块输入由两次 split/append 重建；这里的外延性证明仍是
-- 构造性的坐标分解，完全不枚举 Boolean 赋值。
leftTripleHomExt : {p q r k : ℕ} {f g : Hom (Q ((p + q) + r)) (Q k)}
  → ((x : Vertex (Q p)) (y : Vertex (Q q)) (z : Vertex (Q r))
    → onVertices f (appendPoint (p + q) r (appendPoint p q x y) z)
      ≡ onVertices g (appendPoint (p + q) r (appendPoint p q x y) z))
  → f ≡ g
leftTripleHomExt {p} {q} {r} {k} {f} {g} e =
  appendHomExt {m = p + q} {n = r} {k = k} {f = f} {g = g} λ xy z →
    sym (cong (λ t → onVertices f (appendPoint (p + q) r t z)) (append-split p q xy))
    ∙ e (fst (splitPoint p q xy)) (snd (splitPoint p q xy)) z
    ∙ cong (λ t → onVertices g (appendPoint (p + q) r t z)) (append-split p q xy)

rightTripleHomExt : {p q r k : ℕ} {f g : Hom (Q (p + (q + r))) (Q k)}
  → ((x : Vertex (Q p)) (y : Vertex (Q q)) (z : Vertex (Q r))
    → onVertices f (appendPoint p (q + r) x (appendPoint q r y z))
      ≡ onVertices g (appendPoint p (q + r) x (appendPoint q r y z)))
  → f ≡ g
rightTripleHomExt {p} {q} {r} {k} {f} {g} e =
  appendHomExt {m = p} {n = q + r} {k = k} {f = f} {g = g} λ x yz →
    sym (cong (λ t → onVertices f (appendPoint p (q + r) x t)) (append-split q r yz))
    ∙ e x (fst (splitPoint q r yz)) (snd (splitPoint q r yz))
    ∙ cong (λ t → onVertices g (appendPoint p (q + r) x t)) (append-split q r yz)

cubeAssociator-natural : {p p' q q' r r' : ℕ}
  (f : CubicalMap p p') (g : CubicalMap q q') (h : CubicalMap r r')
  → ((f ⊗c g) ⊗c h) ⋆c cubeAssociator p' q' r'
    ≡ cubeAssociator p q r ⋆c (f ⊗c (g ⊗c h))
cubeAssociator-natural {p} {p'} {q} {q'} {r} {r'} f g h = cubeMapExt
  (leftTripleHomExt {p = p} {q = q} {r = r} {k = p' + (q' + r')}
    {f = underlying (((f ⊗c g) ⊗c h) ⋆c cubeAssociator p' q' r')}
    {g = underlying (cubeAssociator p q r ⋆c (f ⊗c (g ⊗c h)))} λ x y z →
    cong (onVertices (underlying (cubeAssociator p' q' r')))
      (tensor-on-append (f ⊗c g) h (appendPoint p q x y) z)
    ∙ cong (λ xy → onVertices (underlying (cubeAssociator p' q' r'))
        (appendPoint (p' + q') r' xy (onVertices (underlying h) z)))
      (tensor-on-append f g x y)
    ∙ cubeAssociator-on-append p' q' r'
      (onVertices (underlying f) x) (onVertices (underlying g) y) (onVertices (underlying h) z)
    ∙ sym (cong (onVertices (underlying (f ⊗c (g ⊗c h)))) (cubeAssociator-on-append p q r x y z)
      ∙ tensor-on-append f (g ⊗c h) x (appendPoint q r y z)
      ∙ cong (appendPoint p' (q' + r') (onVertices (underlying f) x)) (tensor-on-append g h y z)))

cubeAssociatorInv-natural : {p p' q q' r r' : ℕ}
  (f : CubicalMap p p') (g : CubicalMap q q') (h : CubicalMap r r')
  → (f ⊗c (g ⊗c h)) ⋆c cubeAssociatorInv p' q' r'
    ≡ cubeAssociatorInv p q r ⋆c ((f ⊗c g) ⊗c h)
cubeAssociatorInv-natural {p} {p'} {q} {q'} {r} {r'} f g h = cubeMapExt
  (rightTripleHomExt {p = p} {q = q} {r = r} {k = (p' + q') + r'}
    {f = underlying ((f ⊗c (g ⊗c h)) ⋆c cubeAssociatorInv p' q' r')}
    {g = underlying (cubeAssociatorInv p q r ⋆c ((f ⊗c g) ⊗c h))} λ x y z →
    cong (onVertices (underlying (cubeAssociatorInv p' q' r')))
      (tensor-on-append f (g ⊗c h) x (appendPoint q r y z))
    ∙ cong (λ yz → onVertices (underlying (cubeAssociatorInv p' q' r'))
        (appendPoint p' (q' + r') (onVertices (underlying f) x) yz))
      (tensor-on-append g h y z)
    ∙ cubeAssociatorInv-on-append p' q' r'
      (onVertices (underlying f) x) (onVertices (underlying g) y) (onVertices (underlying h) z)
    ∙ sym (cong (onVertices (underlying ((f ⊗c g) ⊗c h))) (cubeAssociatorInv-on-append p q r x y z)
      ∙ tensor-on-append (f ⊗c g) h (appendPoint p q x y) z
      ∙ cong (λ xy → appendPoint (p' + q') r' xy (onVertices (underlying h) z))
        (tensor-on-append f g x y)))

tensor-left-right : {m n p q : ℕ} (f : CubicalMap m n) (g : CubicalMap p q)
  → (f ⊗c cubeId p) ⋆c (cubeId n ⊗c g) ≡ f ⊗c g
tensor-left-right {n = n} {p} f g =
  sym (tensor-compose f (cubeId n) (cubeId p) g)
  ∙ cong₂ _⊗c_ (Category.⋆IdR CubeCategory f) (Category.⋆IdL CubeCategory g)

tensor-right-left : {m n p q : ℕ} (f : CubicalMap m n) (g : CubicalMap p q)
  → (cubeId m ⊗c g) ⋆c (f ⊗c cubeId q) ≡ f ⊗c g
tensor-right-left {m} {q = q} f g =
  sym (tensor-compose (cubeId m) f g (cubeId q))
  ∙ cong₂ _⊗c_ (Category.⋆IdL CubeCategory f) (Category.⋆IdR CubeCategory g)

tensor-right-id-compose : {l m n : ℕ} (f : CubicalMap l m) (g : CubicalMap m n) (r : ℕ)
  → (f ⋆c g) ⊗c cubeId r ≡ (f ⊗c cubeId r) ⋆c (g ⊗c cubeId r)
tensor-right-id-compose f g r =
  cong ((f ⋆c g) ⊗c_) (sym (Category.⋆IdL CubeCategory (cubeId r)))
  ∙ tensor-compose f g (cubeId r) (cubeId r)

tensor-left-id-compose : (p : ℕ) {l m n : ℕ} (f : CubicalMap l m) (g : CubicalMap m n)
  → cubeId p ⊗c (f ⋆c g) ≡ (cubeId p ⊗c f) ⋆c (cubeId p ⊗c g)
tensor-left-id-compose p f g =
  cong (_⊗c (f ⋆c g)) (sym (Category.⋆IdL CubeCategory (cubeId p)))
  ∙ tensor-compose (cubeId p) (cubeId p) f g
