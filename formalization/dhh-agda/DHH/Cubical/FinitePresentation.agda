{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.FinitePresentation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin; isSetFin)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)
import Cubical.HITs.SetQuotients as SQ
open import DHH.CubeCategory
open import DHH.CubicalNerve

private variable ℓ : Level

-- 有限呈示不要求cell总数有限。每个节点给一个代表立方体，
-- 每条关系给两条有限参数态射；任意维度的退化/重索引由规则生成。
-- 这个语言可容纳边界与open box的有限面数据，而非穷举所有cells。
record Relation {r : ℕ} (dim : Fin r → ℕ) : Type₀ where
  field
    relationDimension : ℕ
    leftNode rightNode : Fin r
    leftMap : CubicalMap relationDimension (dim leftNode)
    rightMap : CubicalMap relationDimension (dim rightNode)
open Relation public

module Presentation (r : ℕ) (dim : Fin r → ℕ)
                    (q : ℕ) (relations : Fin q → Relation dim) where
  Generator : ℕ → Type₀
  Generator n = Σ[ i ∈ Fin r ] CubicalMap n (dim i)

  data Identification (n : ℕ) : Generator n → Generator n → Type₀ where
    identify : (e : Fin q) (u : CubicalMap n (relationDimension (relations e)))
      → Identification n
        (leftNode (relations e) , u ⋆c leftMap (relations e))
        (rightNode (relations e) , u ⋆c rightMap (relations e))

  PresentedCell : ℕ → Type₀
  PresentedCell n = Generator n SQ./ Identification n

  point : {n : ℕ} → (i : Fin r) → CubicalMap n (dim i) → PresentedCell n
  point i u = SQ.[ i , u ]

  actGenerator : {m n : ℕ} → CubicalMap m n → Generator n → Generator m
  actGenerator f (i , u) = i , f ⋆c u

  act-relation : {m n : ℕ} (f : CubicalMap m n)
    (x y : Generator n) → Identification n x y
    → point (fst x) (f ⋆c snd x) ≡ point (fst y) (f ⋆c snd y)
  act-relation f _ _ (identify e u) =
    cong (point (leftNode (relations e)))
      (sym (Category.⋆Assoc CubeCategory f u (leftMap (relations e))))
    ∙ SQ.eq/ _ _ (identify e (f ⋆c u))
    ∙ cong (point (rightNode (relations e)))
      (Category.⋆Assoc CubeCategory f u (rightMap (relations e)))

  act : {m n : ℕ} → CubicalMap m n → PresentedCell n → PresentedCell m
  act f = SQ.rec SQ.squash/ (λ x → SQ.[ actGenerator f x ]) (act-relation f)

  complex : CubicalSet ℓ-zero
  cells complex n = PresentedCell n , SQ.squash/
  reindex complex = act
  reindex-id complex = SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ { (i , u) → cong (point i) (Category.⋆IdL CubeCategory u) })
  reindex-compose complex f g = SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ { (i , u) → cong (point i) (Category.⋆Assoc CubeCategory f g u) })

  nodeCell : (i : Fin r) → Cell complex (dim i)
  nodeCell i = point i (cubeId (dim i))

  node-reindex : (i : Fin r) {n : ℕ} (u : CubicalMap n (dim i))
    → reindex complex u (nodeCell i) ≡ point i u
  node-reindex i u = cong (point i) (Category.⋆IdR CubeCategory u)

  Equation : (A : CubicalSet ℓ) (xs : (i : Fin r) → Cell A (dim i))
    → Relation dim → Type ℓ
  Equation A xs e = reindex A (leftMap e) (xs (leftNode e))
    ≡ reindex A (rightMap e) (xs (rightNode e))

  node-relations : (e : Fin q) → Equation complex nodeCell (relations e)
  node-relations e =
    node-reindex (leftNode (relations e)) (leftMap (relations e))
    ∙ cong (point (leftNode (relations e)))
      (sym (Category.⋆IdL CubeCategory (leftMap (relations e))))
    ∙ SQ.eq/ _ _ (identify e (cubeId (relationDimension (relations e))))
    ∙ cong (point (rightNode (relations e)))
      (Category.⋆IdL CubeCategory (rightMap (relations e)))
    ∙ sym (node-reindex (rightNode (relations e)) (rightMap (relations e)))

  module Interpret (A : CubicalSet ℓ) (xs : (i : Fin r) → Cell A (dim i))
                   (eq : (e : Fin q) → Equation A xs (relations e)) where
    interpretGenerator : (n : ℕ) → Generator n → Cell A n
    interpretGenerator n (i , u) = reindex A u (xs i)

    respects : (n : ℕ) (x y : Generator n) → Identification n x y
      → interpretGenerator n x ≡ interpretGenerator n y
    respects n _ _ (identify e u) =
      reindex-compose A u (leftMap (relations e)) (xs (leftNode (relations e)))
      ∙ cong (reindex A u) (eq e)
      ∙ sym (reindex-compose A u (rightMap (relations e)) (xs (rightNode (relations e))))

    -- 有限生成元先解释，再降商；reindex-compose证明全部自然性。
    -- 关系的长度只影响给出的证书，不限制未来重索引的维数。
    factor : CubicalNatural complex A
    mapCells factor n = SQ.rec (snd (cells A n)) (interpretGenerator n) (respects n)
    natural factor {m} f = SQ.elimProp (λ _ → snd (cells A m) _ _)
      (λ { (i , u) → reindex-compose A f u (xs i) })

    factor-on-node : (i : Fin r) → mapCells factor (dim i) (nodeCell i) ≡ xs i
    factor-on-node i = reindex-id A (xs i)

    factor-unique : (h : CubicalNatural complex A)
      → ((i : Fin r) → mapCells h (dim i) (nodeCell i) ≡ xs i)
      → h ≡ factor
    factor-unique h nodes = cubicalNaturalExt {A = complex} {B = A} {f = h} {g = factor}
      (λ n → SQ.elimProp (λ _ → snd (cells A n) _ _)
        (λ { (i , u) →
          cong (mapCells h n) (sym (node-reindex i u))
          ∙ natural h u (nodeCell i)
          ∙ cong (reindex A u) (nodes i) }))

  -- 一个全局映射的有限节点值自动满足全部原始关系。
  -- 这是呈示的泛性质所需的反向构造，并非额外相容假设。
  extractNodes : (A : CubicalSet ℓ) → CubicalNatural complex A
    → (i : Fin r) → Cell A (dim i)
  extractNodes A h i = mapCells h (dim i) (nodeCell i)

  extractRelations : (A : CubicalSet ℓ) (h : CubicalNatural complex A)
    → (e : Fin q) → Equation A (extractNodes A h) (relations e)
  extractRelations A h e =
    sym (natural h (leftMap (relations e)) (nodeCell (leftNode (relations e))))
    ∙ cong (mapCells h (relationDimension (relations e))) (node-relations e)
    ∙ natural h (rightMap (relations e)) (nodeCell (rightNode (relations e)))

  -- 下一接口：将有限生成元和关系同时提升到共同stage，即能提升
  -- 整个Presented复形的映射。对实际OpenBox还须证明这份呈示确实
  -- 等价于选面子预层；不能仅凭“有限关系”就宣称OpenBox已因子化。
