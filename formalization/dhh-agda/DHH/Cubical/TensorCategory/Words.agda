{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.TensorCategory.Words where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import DHH.Graph
open import DHH.Cubes
open import DHH.CubeCategory
open import DHH.Cubical.TensorCategory.Coordinates

-- 输入有限的 CubeWord，程序把它放在一组坐标中，另一组保持不动。
-- 每个 composeW 递归到两个严格子词；位置证明按 here/there 递归。
-- 因而生成性证书由语法结构构造，无需枚举布尔函数或搜索等价词。
suffixPosition : {n : ℕ} (p : ℕ) → Position n → Position (n + p)
suffixPosition p here = here
suffixPosition p (there i) = there (suffixPosition p i)

suffixWord : {m n : ℕ} → CubeWord m n → (p : ℕ) → CubeWord (m + p) (n + p)
suffixWord identityW p = identityW
suffixWord (faceW i b) p = faceW (suffixPosition p i) b
suffixWord (deleteW i) p = deleteW (suffixPosition p i)
suffixWord (minW i) p = minW (suffixPosition p i)
suffixWord (maxW i) p = maxW (suffixPosition p i)
suffixWord (composeW f g) p = composeW (suffixWord f p) (suffixWord g p)

underWord : {m n : ℕ} → CubeWord m n → CubeWord (suc m) (suc n)
underWord identityW = identityW
underWord (faceW i b) = faceW (there i) b
underWord (deleteW i) = deleteW (there i)
underWord (minW i) = minW (there i)
underWord (maxW i) = maxW (there i)
underWord (composeW f g) = composeW (underWord f) (underWord g)

prefixWord : (p : ℕ) {m n : ℕ} → CubeWord m n → CubeWord (p + m) (p + n)
prefixWord zero w = w
prefixWord (suc p) w = underWord (prefixWord p w)

suffix-insert : (p : ℕ) {n : ℕ} (i : Position (suc n)) (b : Bool)
  (x : Vertex (Q n)) (y : Vertex (Q p))
  → insert (suffixPosition p i) b (appendPoint n p x y)
    ≡ appendPoint (suc n) p (insert i b x) y
suffix-insert p here b x y = refl
suffix-insert p {suc n} (there i) b (a , x) y = cong (a ,_) (suffix-insert p i b x y)

suffix-delete : (p : ℕ) {n : ℕ} (i : Position (suc n))
  (x : Vertex (Q (suc n))) (y : Vertex (Q p))
  → delete (suffixPosition p i) (appendPoint (suc n) p x y)
    ≡ appendPoint n p (delete i x) y
suffix-delete p here (a , x) y = refl
suffix-delete p {suc n} (there i) (a , x) y = cong (a ,_) (suffix-delete p i x y)

suffix-merge : (p : ℕ) {n : ℕ} (i : Position (suc n)) (op : Bool → Bool → Bool)
  (x : Vertex (Q (suc (suc n)))) (y : Vertex (Q p))
  → merge (suffixPosition p i) op (appendPoint (suc (suc n)) p x y)
    ≡ appendPoint (suc n) p (merge i op x) y
suffix-merge p here op (a , b , x) y = refl
suffix-merge p {suc n} (there i) op (a , x) y = cong (a ,_) (suffix-merge p i op x y)

suffix-evaluate : {m n : ℕ} (w : CubeWord m n) (p : ℕ)
  (x : Vertex (Q m)) (y : Vertex (Q p))
  → onVertices (evaluate (suffixWord w p)) (appendPoint m p x y)
    ≡ appendPoint n p (onVertices (evaluate w) x) y
suffix-evaluate identityW p x y = refl
suffix-evaluate (faceW i b) p x y = suffix-insert p i b x y
suffix-evaluate (deleteW i) p x y = suffix-delete p i x y
suffix-evaluate (minW i) p x y = suffix-merge p i meetBool x y
suffix-evaluate (maxW i) p x y = suffix-merge p i joinBool x y
suffix-evaluate (composeW f g) p x y =
  cong (onVertices (evaluate (suffixWord g p))) (suffix-evaluate f p x y)
  ∙ suffix-evaluate g p (onVertices (evaluate f) x) y

under-evaluate : {m n : ℕ} (w : CubeWord m n) (a : Bool) (x : Vertex (Q m))
  → onVertices (evaluate (underWord w)) (a , x) ≡ (a , onVertices (evaluate w) x)
under-evaluate identityW a x = refl
under-evaluate (faceW i b) a x = refl
under-evaluate (deleteW i) a x = refl
under-evaluate (minW i) a x = refl
under-evaluate (maxW i) a x = refl
under-evaluate (composeW f g) a x =
  cong (onVertices (evaluate (underWord g))) (under-evaluate f a x)
  ∙ under-evaluate g a (onVertices (evaluate f) x)

prefix-evaluate : (p : ℕ) {m n : ℕ} (w : CubeWord m n)
  (x : Vertex (Q p)) (y : Vertex (Q m))
  → onVertices (evaluate (prefixWord p w)) (appendPoint p m x y)
    ≡ appendPoint p n x (onVertices (evaluate w) y)
prefix-evaluate zero w tt y = refl
prefix-evaluate (suc p) w (a , x) y =
  under-evaluate (prefixWord p w) a (appendPoint p _ x y)
  ∙ cong (a ,_) (prefix-evaluate p w x y)

tensorWord : {m n p q : ℕ} → CubeWord m n → CubeWord p q → CubeWord (m + p) (n + q)
tensorWord {n = n} {p = p} f g = composeW (suffixWord f p) (prefixWord n g)

tensor-evaluate-on-append : {m n p q : ℕ} (f : CubeWord m n) (g : CubeWord p q)
  (x : Vertex (Q m)) (y : Vertex (Q p))
  → onVertices (evaluate (tensorWord f g)) (appendPoint m p x y)
    ≡ appendPoint n q (onVertices (evaluate f) x) (onVertices (evaluate g) y)
tensor-evaluate-on-append {n = n} {p = p} f g x y =
  cong (onVertices (evaluate (prefixWord n g))) (suffix-evaluate f p x y)
  ∙ prefix-evaluate n g (onVertices (evaluate f) x) y

tensor-evaluate : {m n p q : ℕ} (f : CubeWord m n) (g : CubeWord p q)
  → evaluate (tensorWord f g) ≡ tensorHom {m} {n} {p} {q} (evaluate f) (evaluate g)
tensor-evaluate {m} {n} {p} {q} f g = appendHomExt {m = m} {n = p} {k = n + q} λ x y →
  tensor-evaluate-on-append f g x y
  ∙ sym (tensorHom-on-append {m} {n} {p} {q} (evaluate f) (evaluate g) x y)

-- 这里证明闭包而未给 CubeWord 相等的判定程序；任意图映射并没有
-- 因此成为立方态射。两输入必须各自携带真实生成性证书。
