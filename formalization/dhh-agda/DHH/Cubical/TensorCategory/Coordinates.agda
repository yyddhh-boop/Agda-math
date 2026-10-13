{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.TensorCategory.Coordinates where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.Cubes
open import DHH.FiniteInterval using (UnitInterval)
open import DHH.Enrichment.GraphHomCoherence using (boxAssociate; boxLeftUnit)

-- 按左块长度递归拼接/拆分坐标。Q 的边仍只改变一个坐标，故对应的是
-- 图 BOX；这一步不是预层逐度积，也不把所有图映射当成立方范畴态射。
appendPoint : (m n : ℕ) → Vertex (Q m) → Vertex (Q n) → Vertex (Q (m + n))
appendPoint zero n tt y = y
appendPoint (suc m) n (a , x) y = a , appendPoint m n x y

splitPoint : (m n : ℕ) → Vertex (Q (m + n)) → Vertex (Q m) × Vertex (Q n)
splitPoint zero n z = tt , z
splitPoint (suc m) n (a , z) = (a , fst (splitPoint m n z)) , snd (splitPoint m n z)

split-append : (m n : ℕ) (x : Vertex (Q m)) (y : Vertex (Q n))
  → splitPoint m n (appendPoint m n x y) ≡ (x , y)
split-append zero n tt y = refl
split-append (suc m) n (a , x) y =
  cong (λ pair → (a , fst pair) , snd pair) (split-append m n x y)

append-split : (m n : ℕ) (z : Vertex (Q (m + n)))
  → appendPoint m n (fst (splitPoint m n z)) (snd (splitPoint m n z)) ≡ z
append-split zero n z = refl
append-split (suc m) n (a , z) = cong (a ,_) (append-split m n z)

splitPointIso : (m n : ℕ) → Iso (Vertex (Q (m + n))) (Vertex (Q m) × Vertex (Q n))
Iso.fun (splitPointIso m n) = splitPoint m n
Iso.inv (splitPointIso m n) pair = appendPoint m n (fst pair) (snd pair)
Iso.rightInv (splitPointIso m n) pair = split-append m n (fst pair) (snd pair)
Iso.leftInv (splitPointIso m n) = append-split m n

private
  boxUnassociate : (A B C : Graph ℓ-zero) → Hom (A BOX (B BOX C)) ((A BOX B) BOX C)
  onVertices (boxUnassociate A B C) (a , b , c) = (a , b) , c
  preserves (boxUnassociate A B C) {x = (x , y , z)} {y = (x' , y' , z')} =
    PT.rec (adj-isProp ((A BOX B) BOX C) ((x , y) , z) ((x' , y') , z')) λ where
    (inl (a , bc)) → PT.rec (adj-isProp ((A BOX B) BOX C) ((x , y) , z) ((x' , y') , z'))
      (λ where
        (inl (b , c)) → ∣ inl ((λ i → a i , b i) , c) ∣₁
        (inr (b , c)) → ∣ inr (∣ inl (a , b) ∣₁ , c) ∣₁) bc
    (inr (a , bc)) → ∣ inr (∣ inr (a , cong fst bc) ∣₁ , cong snd bc) ∣₁

appendHom : (m n : ℕ) → Hom (Q m BOX Q n) (Q (m + n))
onVertices (appendHom m n) pair = appendPoint m n (fst pair) (snd pair)
preserves (appendHom zero n) = preserves (boxLeftUnit (Q n))
preserves (appendHom (suc m) n) = preserves
  (boxHom (idHom UnitInterval) (appendHom m n) ∘g boxAssociate UnitInterval (Q m) (Q n))

splitHom : (m n : ℕ) → Hom (Q (m + n)) (Q m BOX Q n)
onVertices (splitHom m n) = splitPoint m n
preserves (splitHom zero n) e = ∣ inl (refl , e) ∣₁
preserves (splitHom (suc m) n) = preserves
  (boxUnassociate UnitInterval (Q m) (Q n) ∘g boxHom (idHom UnitInterval) (splitHom m n))

split-append-Hom : (m n : ℕ) → splitHom m n ∘g appendHom m n ≡ idHom (Q m BOX Q n)
split-append-Hom m n = homExt λ pair → split-append m n (fst pair) (snd pair)

append-split-Hom : (m n : ℕ) → appendHom m n ∘g splitHom m n ≡ idHom (Q (m + n))
append-split-Hom m n = homExt (append-split m n)

-- 对任意图映射可先做分块图映射；只有下一模块的 generated 证明
-- 才能保证输入来自 CubeCategory 时，输出仍属于 CubeCategory。
tensorHom : {m n p q : ℕ} → Hom (Q m) (Q n) → Hom (Q p) (Q q)
  → Hom (Q (m + p)) (Q (n + q))
tensorHom {m} {n} {p} {q} f g = appendHom n q ∘g boxHom f g ∘g splitHom m p

tensorHom-on-append : {m n p q : ℕ} (f : Hom (Q m) (Q n)) (g : Hom (Q p) (Q q))
  (x : Vertex (Q m)) (y : Vertex (Q p))
  → onVertices (tensorHom {m} {n} {p} {q} f g) (appendPoint m p x y)
    ≡ appendPoint n q (onVertices f x) (onVertices g y)
tensorHom-on-append {m} {n} {p} {q} f g x y =
  cong (λ pair → appendPoint n q (onVertices f (fst pair)) (onVertices g (snd pair)))
    (split-append m p x y)

-- 使用拆分的逆律，把任意输入点上的证明缩回两块输入上的证明。
appendHomExt : {m n k : ℕ} {f g : Hom (Q (m + n)) (Q k)}
  → ((x : Vertex (Q m)) (y : Vertex (Q n))
      → onVertices f (appendPoint m n x y) ≡ onVertices g (appendPoint m n x y))
  → f ≡ g
appendHomExt {m} {n} {f = f} {g} e = homExt λ z →
  sym (cong (onVertices f) (append-split m n z))
    ∙ e (fst (splitPoint m n z)) (snd (splitPoint m n z))
    ∙ cong (onVertices g) (append-split m n z)

tensorHom-id : (m n : ℕ) → tensorHom {m} {m} {n} {n} (idHom (Q m)) (idHom (Q n)) ≡ idHom (Q (m + n))
tensorHom-id m n = homExt (append-split m n)

tensorHom-compose : {m n k p q r : ℕ}
  (f : Hom (Q m) (Q n)) (f' : Hom (Q n) (Q k))
  (g : Hom (Q p) (Q q)) (g' : Hom (Q q) (Q r))
  → tensorHom {m} {k} {p} {r} (f' ∘g f) (g' ∘g g)
    ≡ tensorHom {n} {k} {q} {r} f' g' ∘g tensorHom {m} {n} {p} {q} f g
tensorHom-compose {m} {n} {k} {p} {q} {r} f f' g g' = appendHomExt {m = m} {n = p} {k = k + r} λ x y →
  tensorHom-on-append {m} {k} {p} {r} (f' ∘g f) (g' ∘g g) x y
    ∙ sym (cong (onVertices (tensorHom {n} {k} {q} {r} f' g')) (tensorHom-on-append {m} {n} {p} {q} f g x y)
      ∙ tensorHom-on-append {n} {k} {q} {r} f' g' (onVertices f x) (onVertices g y))
