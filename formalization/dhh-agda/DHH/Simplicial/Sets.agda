{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base using (Functor)
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Presented
open import DHH.Simplicial.PresentationCompleteness

private variable ℓ ℓ' ℓ'' : Level

-- 原文 quasicategory 是单纯集合：明确保留每阶 cell 的集合性。
-- 重索引接收全部单调映射，包含所有面与退化恒等式。
-- 后续 coherent nerve 的 cell 若包含非集合对象类型，不能直接装入此类型；
-- 这项检查能防止把内部高阶对象默认为经典对象集合。
record SimplicialSet (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    simplexes : ℕ → hSet ℓ
    reindexS : {m n : ℕ} → OrdinalMap m n → fst (simplexes n) → fst (simplexes m)
    reindexS-id : {n : ℕ} (c : fst (simplexes n)) → reindexS (ordinalId n) c ≡ c
    reindexS-compose : {m n k : ℕ} (f : OrdinalMap m n) (g : OrdinalMap n k)
                    (c : fst (simplexes k))
                  → reindexS (f ⋆o g) c ≡ reindexS f (reindexS g c)
open SimplicialSet public

SCell : SimplicialSet ℓ → ℕ → Type ℓ
SCell A n = fst (simplexes A n)

record SimplicialNatural (A : SimplicialSet ℓ) (B : SimplicialSet ℓ')
                     : Type (ℓ-max ℓ ℓ') where
  field
    mapS : (n : ℕ) → SCell A n → SCell B n
    naturalS : {m n : ℕ} (f : OrdinalMap m n) (c : SCell A n)
            → mapS m (reindexS A f c) ≡ reindexS B f (mapS n c)
open SimplicialNatural public

simplicialNaturalExt : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
                    {f g : SimplicialNatural A B}
                  → ((n : ℕ) (c : SCell A n) → mapS f n c ≡ mapS g n c)
                  → f ≡ g
mapS (simplicialNaturalExt p i) n c = p n c i
naturalS (simplicialNaturalExt {A = A} {B = B} {f = f} {g = g} p i) {m} {n} u c =
  isProp→PathP
    {B = λ j → p m (reindexS A u c) j ≡ reindexS B u (p n c j)}
    (λ i → snd (simplexes B m) (p m (reindexS A u c) i)
      (reindexS B u (p n c i)))
    (naturalS f u c) (naturalS g u c) i

simplicialId : (A : SimplicialSet ℓ) → SimplicialNatural A A
mapS (simplicialId A) n c = c
naturalS (simplicialId A) u c = refl

infixl 20 _⋆s_
_⋆s_ : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'} {C : SimplicialSet ℓ''}
       → SimplicialNatural A B → SimplicialNatural B C → SimplicialNatural A C
mapS (f ⋆s g) n c = mapS g n (mapS f n c)
naturalS (f ⋆s g) {m} u c =
  cong (mapS g m) (naturalS f u c) ∙ naturalS g u (mapS f _ c)

NaturalProof : (A : SimplicialSet ℓ) (B : SimplicialSet ℓ')
             → ((n : ℕ) → SCell A n → SCell B n) → Type (ℓ-max ℓ ℓ')
NaturalProof A B f = (m n : ℕ) (u : OrdinalMap m n) (c : SCell A n)
                   → f m (reindexS A u c) ≡ reindexS B u (f n c)

naturalSProof-isProp : (A : SimplicialSet ℓ) (B : SimplicialSet ℓ')
                     (f : (n : ℕ) → SCell A n → SCell B n)
                   → isProp (NaturalProof A B f)
naturalSProof-isProp A B f = isPropΠ λ m → isPropΠ λ n →
  isPropΠ λ u → isPropΠ λ c → snd (simplexes B m) _ _

NaturalΣ : (A : SimplicialSet ℓ) (B : SimplicialSet ℓ') → Type (ℓ-max ℓ ℓ')
NaturalΣ A B = Σ[ f ∈ ((n : ℕ) → SCell A n → SCell B n) ] NaturalProof A B f

naturalSToΣ : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
             → SimplicialNatural A B → NaturalΣ A B
naturalSToΣ f = mapS f , λ m n u c → naturalS f u c

ΣToNatural : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
             → NaturalΣ A B → SimplicialNatural A B
mapS (ΣToNatural (f , p)) = f
naturalS (ΣToNatural (f , p)) {m} {n} = p m n

isSetSimplicialNatural : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
                   → isSet (SimplicialNatural A B)
isSetSimplicialNatural {A = A} {B = B} =
  isSetRetract naturalSToΣ ΣToNatural (λ f → simplicialNaturalExt (λ _ _ → refl))
    (isSetΣSndProp (isSetΠ2 (λ n _ → snd (simplexes B n)))
      (naturalSProof-isProp A B))

SimplicialSetCategory : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Category.ob (SimplicialSetCategory ℓ) = SimplicialSet ℓ
Category.Hom[_,_] (SimplicialSetCategory ℓ) = SimplicialNatural
Category.id (SimplicialSetCategory ℓ) {x = A} = simplicialId A
Category._⋆_ (SimplicialSetCategory ℓ) = _⋆s_
Category.⋆IdL (SimplicialSetCategory ℓ) f = simplicialNaturalExt (λ _ _ → refl)
Category.⋆IdR (SimplicialSetCategory ℓ) f = simplicialNaturalExt (λ _ _ → refl)
Category.⋆Assoc (SimplicialSetCategory ℓ) f g h = simplicialNaturalExt (λ _ _ → refl)
Category.isSetHom (SimplicialSetCategory ℓ) = isSetSimplicialNatural


RepresentableSimplex : ℕ → SimplicialSet ℓ-zero
simplexes (RepresentableSimplex n) m = OrdinalMap m n , isSetOrdinalMap
reindexS (RepresentableSimplex n) f g = f ⋆o g
reindexS-id (RepresentableSimplex n) g = Category.⋆IdL Delta g
reindexS-compose (RepresentableSimplex n) f g h = Category.⋆Assoc Delta f g h

classifySimplex : {n : ℕ} (A : SimplicialSet ℓ) (c : SCell A n)
  → SimplicialNatural (RepresentableSimplex n) A
mapS (classifySimplex A c) m u = reindexS A u c
naturalS (classifySimplex A c) f g = reindexS-compose A f g c

simplex-classifier-evaluation : {n : ℕ} (A : SimplicialSet ℓ) (c : SCell A n)
  → mapS (classifySimplex A c) n (ordinalId n) ≡ c
simplex-classifier-evaluation A c = reindexS-id A c

every-simplex-natural-classified : {n : ℕ} (A : SimplicialSet ℓ)
  (η : SimplicialNatural (RepresentableSimplex n) A)
  → classifySimplex A (mapS η n (ordinalId n)) ≡ η
every-simplex-natural-classified {n = n} A η = simplicialNaturalExt λ m u →
  sym (naturalS η u (ordinalId n)) ∙ cong (mapS η m) (Category.⋆IdR Delta u)

-- 复用原关系商的完整性：先把具体序数映射转换为已证规范词，再重索引。
-- 这里没有假设 Δ 呈示等价；该互逆函子已经由结构归纳证明。
fromPresented : PresentedSimplicialSet ℓ → SimplicialSet ℓ
simplexes (fromPresented A) = cellsP A
reindexS (fromPresented A) f = actPresented A (inversePresentationMap f)
reindexS-id (fromPresented A) c =
  cong (λ u → actPresented A u c) (Functor.F-id presentationInverse)
reindexS-compose (fromPresented A) f g c =
  cong (λ u → actPresented A u c) (Functor.F-seq presentationInverse f g)
  ∙ cong (λ h → h c) (action-compose A (inversePresentationMap f) (inversePresentationMap g))
