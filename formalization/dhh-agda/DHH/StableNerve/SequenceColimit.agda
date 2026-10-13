{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.SequenceColimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.CubeCategory
open import DHH.CubicalNerve

private variable ℓ ℓ' : Level

-- 构造视角：先给自然数索引的阶段 A 和一步过渡 s，再以带阶段的 cell
-- 及 Step 关系取集合商。定义无限对象不需要运行一个永不结束的展开循环。
-- SQ.rec 用阶段上的相容映射定义商上的映射；factor-unique 证明唯一性。
-- 商未提供规范代表元、等价判定或“相等时找到共同阶段”的有效算法；
-- 此处也未证明它是同伦余极限。后续递归研究须保留这些区别。
module Colimit (A : ℕ → CubicalSet ℓ)
               (s : (k : ℕ) → CubicalNatural (A k) (A (suc k))) where

  Tagged : ℕ → Type ℓ
  Tagged n = Σ[ k ∈ ℕ ] Cell (A k) n

  data Step (n : ℕ) : Tagged n → Tagged n → Type ℓ where
    step : {k : ℕ} (c : Cell (A k) n)
      → Step n (k , c) (suc k , mapCells (s k) n c)

  Points : ℕ → Type ℓ
  Points n = Tagged n SQ./ Step n

  point : (n : ℕ) → Tagged n → Points n
  point n = SQ.[_]

  actTagged : {m n : ℕ} → CubicalMap m n → Tagged n → Tagged m
  actTagged u (k , c) = k , reindex (A k) u c

  actStep : {m n : ℕ} (u : CubicalMap m n) (x y : Tagged n) → Step n x y
    → point m (actTagged u x) ≡ point m (actTagged u y)
  actStep {m} u (k , c) .(suc k , mapCells (s k) _ c) (step c) =
    SQ.eq/ {R = Step m} _ _ (step (reindex (A k) u c))
    ∙ cong (λ d → point m (suc k , d)) (natural (s k) u c)

  act : {m n : ℕ} → CubicalMap m n → Points n → Points m
  act {m} u = SQ.rec SQ.squash/ (λ x → point m (actTagged u x)) (actStep u)

  colimitCubical : CubicalSet ℓ
  cells colimitCubical n = Points n , SQ.squash/
  reindex colimitCubical = act
  reindex-id colimitCubical {n} = SQ.elimProp (λ c → SQ.squash/ _ _)
    (λ { (k , c) → cong (λ d → point n (k , d)) (reindex-id (A k) c) })
  reindex-compose colimitCubical {m} f g = SQ.elimProp (λ c → SQ.squash/ _ _)
    (λ { (k , c) → cong (λ d → point m (k , d)) (reindex-compose (A k) f g c) })

  include : (k : ℕ) → CubicalNatural (A k) colimitCubical
  mapCells (include k) n c = point n (k , c)
  natural (include k) u c = refl

  include-step : (k : ℕ) → s k ⋆n include (suc k) ≡ include k
  include-step k = cubicalNaturalExt (λ n c → sym (SQ.eq/ {R = Step n} _ _ (step c)))

  record Cocone (B : CubicalSet ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      family : (k : ℕ) → CubicalNatural (A k) B
      compatible : (k n : ℕ) (c : Cell (A k) n)
        → mapCells (family (suc k)) n (mapCells (s k) n c) ≡ mapCells (family k) n c
  open Cocone public

  module _ {B : CubicalSet ℓ'} (K : Cocone B) where
    factorCells : (n : ℕ) → Points n → Cell B n
    factorCells n = SQ.rec (snd (cells B n))
      (λ { (k , c) → mapCells (family K k) n c })
      (λ { (k , c) .(suc k , mapCells (s k) n c) (step c) → sym (compatible K k n c) })

    factor : CubicalNatural colimitCubical B
    mapCells factor = factorCells
    natural factor {m} u = SQ.elimProp (λ c → snd (cells B m) _ _)
      (λ { (k , c) → natural (family K k) u c })

    factor-on-stage : (k : ℕ) → include k ⋆n factor ≡ family K k
    factor-on-stage k = cubicalNaturalExt (λ n c → refl)

    factor-unique : (g : CubicalNatural colimitCubical B)
      → ((k : ℕ) → include k ⋆n g ≡ family K k) → g ≡ factor
    factor-unique g e = cubicalNaturalExt λ n → SQ.elimProp
      (λ c → snd (cells B n) _ _)
      (λ { (k , c) → cong (λ h → mapCells h n c) (e k) })
