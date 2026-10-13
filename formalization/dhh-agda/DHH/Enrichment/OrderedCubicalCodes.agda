{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.OrderedCubicalCodes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Ordinal.Base using (Ord; isSetOrd)
open import Cubical.Relation.Binary.Order.Woset.Base using (WosetStr)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base using (Functor)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.Kan

private variable ℓ ℓ' : Level

-- 与图对象编码相同，每阶载体保留刚性的 ordinal 结构，但重索引
-- 函数与以后定义的自然变换均无需保序。立方体范畴的所有态射都
-- 参与这里的函子律，故编码没有只截取有限次数或有限个面公式。
OrderedDegrees : (ℓ : Level) → Type (ℓ-suc ℓ)
OrderedDegrees ℓ = ℕ → Ord {ℓ}

OrderedReindex : OrderedDegrees ℓ → Type ℓ
OrderedReindex D = (m n : ℕ) → CubicalMap m n → ⟨ D n ⟩ → ⟨ D m ⟩

OrderedCubicalLaws : (D : OrderedDegrees ℓ) → OrderedReindex D → Type ℓ
OrderedCubicalLaws D R =
  ((n : ℕ) (c : ⟨ D n ⟩) → R n n (cubeId n) c ≡ c) ×
  ((m n k : ℕ) (f : CubicalMap m n) (g : CubicalMap n k) (c : ⟨ D k ⟩)
    → R m k (f ⋆c g) c ≡ R m n f (R n k g c))

orderedCubicalLaws-isProp : (D : OrderedDegrees ℓ) (R : OrderedReindex D)
  → isProp (OrderedCubicalLaws D R)
orderedCubicalLaws-isProp D R =
  isProp× (isPropΠ2 (λ n c → WosetStr.is-set (snd (D n)) _ _))
    (isPropΠ3 (λ m n k → isPropΠ3
      (λ f g c → WosetStr.is-set (snd (D m)) _ _)))

orderedReindex-isSet : (D : OrderedDegrees ℓ) → isSet (OrderedReindex D)
orderedReindex-isSet D = isSetΠ3 λ m n u →
  isSetΠ (λ c → WosetStr.is-set (snd (D m)))

OrderedCubicalCode : (ℓ : Level) → Type (ℓ-suc ℓ)
OrderedCubicalCode ℓ = Σ[ D ∈ OrderedDegrees ℓ ]
  Σ[ R ∈ OrderedReindex D ] OrderedCubicalLaws D R

orderedCubicalCode-isSet : isSet (OrderedCubicalCode ℓ)
orderedCubicalCode-isSet = isSetΣ (isSetΠ (λ _ → isSetOrd)) λ D →
  isSetΣSndProp (orderedReindex-isSet D) (orderedCubicalLaws-isProp D)

decodeOrderedCubical : OrderedCubicalCode ℓ → CubicalSet ℓ
cells (decodeOrderedCubical (D , R , laws)) n =
  ⟨ D n ⟩ , WosetStr.is-set (snd (D n))
reindex (decodeOrderedCubical (D , R , laws)) {m} {n} = R m n
reindex-id (decodeOrderedCubical (D , R , laws)) {n} = fst laws n
reindex-compose (decodeOrderedCubical (D , R , laws)) {m} {n} {k} = snd laws m n k

-- 输入是整族已指定的各阶良序，并非各阶良序“截断存在”的命题。
-- 从后一种命题自动得到此整族数据会添加选择义务，下面不做这一步。
DegreeOrders : CubicalSet ℓ → Type (ℓ-suc ℓ)
DegreeOrders {ℓ} A = (n : ℕ) → WosetStr ℓ (Cell A n)

encodeOrderedCubical : (A : CubicalSet ℓ) → DegreeOrders A → OrderedCubicalCode ℓ
encodeOrderedCubical A orders =
  (λ n → Cell A n , orders n) ,
  (λ m n u → reindex A u) ,
  ((λ n c → reindex-id A c) , λ m n k f g c → reindex-compose A f g c)

-- 解码只可能换掉集合性的证明；所有载体与运算保持原输入。
-- 证明无须选择自然变换，也不依赖任何 Kan 填充程序。
orderedCubicalDecodeEncode : (A : CubicalSet ℓ) (orders : DegreeOrders A)
  → decodeOrderedCubical (encodeOrderedCubical A orders) ≡ A
cells (orderedCubicalDecodeEncode A orders i) n = Cell A n ,
  isPropIsSet (WosetStr.is-set (orders n)) (snd (cells A n)) i
reindex (orderedCubicalDecodeEncode A orders i) = reindex A
reindex-id (orderedCubicalDecodeEncode A orders i) = reindex-id A
reindex-compose (orderedCubicalDecodeEncode A orders i) = reindex-compose A

record CubicalCodeIso (A : CubicalSet ℓ) (B : CubicalSet ℓ')
  : Type (ℓ-max ℓ ℓ') where
  field
    cubicalForward : CubicalNatural A B
    cubicalBackward : CubicalNatural B A
    cubicalSection : cubicalBackward ⋆n cubicalForward ≡ cubicalId B
    cubicalRetraction : cubicalForward ⋆n cubicalBackward ≡ cubicalId A
open CubicalCodeIso public

orderedCubicalRepresentation : (A : CubicalSet ℓ) (orders : DegreeOrders A)
  → CubicalCodeIso (decodeOrderedCubical (encodeOrderedCubical A orders)) A
mapCells (cubicalForward (orderedCubicalRepresentation A orders)) n c = c
natural (cubicalForward (orderedCubicalRepresentation A orders)) u c = refl
mapCells (cubicalBackward (orderedCubicalRepresentation A orders)) n c = c
natural (cubicalBackward (orderedCubicalRepresentation A orders)) u c = refl
cubicalSection (orderedCubicalRepresentation A orders) = cubicalNaturalExt (λ _ _ → refl)
cubicalRetraction (orderedCubicalRepresentation A orders) = cubicalNaturalExt (λ _ _ → refl)

OrderedCubicalCategory : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Category.ob (OrderedCubicalCategory ℓ) = OrderedCubicalCode ℓ
Category.Hom[_,_] (OrderedCubicalCategory ℓ) c d =
  CubicalNatural (decodeOrderedCubical c) (decodeOrderedCubical d)
Category.id (OrderedCubicalCategory ℓ) {x = c} = cubicalId (decodeOrderedCubical c)
Category._⋆_ (OrderedCubicalCategory ℓ) = _⋆n_
Category.⋆IdL (OrderedCubicalCategory ℓ) f = cubicalNaturalExt (λ _ _ → refl)
Category.⋆IdR (OrderedCubicalCategory ℓ) f = cubicalNaturalExt (λ _ _ → refl)
Category.⋆Assoc (OrderedCubicalCategory ℓ) f g h = cubicalNaturalExt (λ _ _ → refl)
Category.isSetHom (OrderedCubicalCategory ℓ) = isSetCubicalNatural

decodeOrderedCubicalFunctor : (ℓ : Level)
  → Functor (OrderedCubicalCategory ℓ) (CubicalSetCategory ℓ)
Functor.F-ob (decodeOrderedCubicalFunctor ℓ) = decodeOrderedCubical
Functor.F-hom (decodeOrderedCubicalFunctor ℓ) f = f
Functor.F-id (decodeOrderedCubicalFunctor ℓ) = refl
Functor.F-seq (decodeOrderedCubicalFunctor ℓ) f g = refl

-- Kan 性在项目中是每个实际 open box 填充的截断存在，并已证明为命题。
-- 将此命题附到严格对象编码上仍得到集合；没有偷偷加入选定 fillers。
OrderedKanCode : (ℓ : Level) → Type (ℓ-suc ℓ)
OrderedKanCode ℓ = Σ[ c ∈ OrderedCubicalCode ℓ ] IsKan (decodeOrderedCubical c)

orderedKanCode-isSet : isSet (OrderedKanCode ℓ)
orderedKanCode-isSet = isSetΣSndProp orderedCubicalCode-isSet
  (λ c → isPropIsKan (decodeOrderedCubical c))

encodeOrderedKan : (A : CubicalSet ℓ) (orders : DegreeOrders A)
  → IsKan A → OrderedKanCode ℓ
encodeOrderedKan A orders kan = encodeOrderedCubical A orders ,
  subst IsKan (sym (orderedCubicalDecodeEncode A orders)) kan

-- 精确覆盖范围是“附带 DegreeOrders 的 Kan 预层”。本模块既不
-- 宣称全部内部 CubicalSet 都可良序化，也不提供 N∞ 的 Kan 性。
