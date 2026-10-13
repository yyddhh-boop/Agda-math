{-# OPTIONS --cubical --safe #-}

module DHH.CubicalNerve where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base using (Functor)
open import DHH.Graph
open import DHH.GraphSets
open import DHH.Cubes hiding (nerveMap)
open import DHH.CubeCategory

private
  variable ℓ ℓ' ℓ'' : Level

-- A presheaf of SETS on the concrete cube category with connections.
-- Since reindexing accepts every morphism of CubeCategory, this record
-- includes all face/degeneracy/connection identities, rather than a
-- selected finite list of adjacent-coordinate formulae.
-- 构造视角：cells 是按维数索引的一族集合，reindex 是对给定 cell 的操作。
-- 定义预层并不要求列举所有 cell；无限图也可使用这些结构性操作和函子律。
record CubicalSet (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    cells : ℕ → hSet ℓ
    reindex : {m n : ℕ} → CubicalMap m n → fst (cells n) → fst (cells m)
    reindex-id : {n : ℕ} (c : fst (cells n)) → reindex (cubeId n) c ≡ c
    reindex-compose : {m n k : ℕ} (f : CubicalMap m n) (g : CubicalMap n k)
                    (c : fst (cells k))
                  → reindex (f ⋆c g) c ≡ reindex f (reindex g c)
open CubicalSet public

Cell : CubicalSet ℓ → ℕ → Type ℓ
Cell A n = fst (cells A n)

record CubicalNatural (A : CubicalSet ℓ) (B : CubicalSet ℓ')
                     : Type (ℓ-max ℓ ℓ') where
  field
    mapCells : (n : ℕ) → Cell A n → Cell B n
    natural : {m n : ℕ} (f : CubicalMap m n) (c : Cell A n)
            → mapCells m (reindex A f c) ≡ reindex B f (mapCells n c)
open CubicalNatural public

cubicalNaturalExt : {A : CubicalSet ℓ} {B : CubicalSet ℓ'}
                    {f g : CubicalNatural A B}
                  → ((n : ℕ) (c : Cell A n) → mapCells f n c ≡ mapCells g n c)
                  → f ≡ g
mapCells (cubicalNaturalExt p i) n c = p n c i
natural (cubicalNaturalExt {A = A} {B = B} {f = f} {g = g} p i) {m} {n} u c =
  isProp→PathP
    {B = λ j → p m (reindex A u c) j ≡ reindex B u (p n c j)}
    (λ i → snd (cells B m) (p m (reindex A u c) i)
      (reindex B u (p n c i)))
    (natural f u c) (natural g u c) i

cubicalId : (A : CubicalSet ℓ) → CubicalNatural A A
mapCells (cubicalId A) n c = c
natural (cubicalId A) u c = refl

infixl 20 _⋆n_
_⋆n_ : {A : CubicalSet ℓ} {B : CubicalSet ℓ'} {C : CubicalSet ℓ''}
       → CubicalNatural A B → CubicalNatural B C → CubicalNatural A C
mapCells (f ⋆n g) n c = mapCells g n (mapCells f n c)
natural (f ⋆n g) {m} u c =
  cong (mapCells g m) (natural f u c) ∙ natural g u (mapCells f _ c)

NaturalProof : (A : CubicalSet ℓ) (B : CubicalSet ℓ')
             → ((n : ℕ) → Cell A n → Cell B n) → Type (ℓ-max ℓ ℓ')
NaturalProof A B f = (m n : ℕ) (u : CubicalMap m n) (c : Cell A n)
                   → f m (reindex A u c) ≡ reindex B u (f n c)

naturalProof-isProp : (A : CubicalSet ℓ) (B : CubicalSet ℓ')
                     (f : (n : ℕ) → Cell A n → Cell B n)
                   → isProp (NaturalProof A B f)
naturalProof-isProp A B f = isPropΠ λ m → isPropΠ λ n →
  isPropΠ λ u → isPropΠ λ c → snd (cells B m) _ _

NaturalΣ : (A : CubicalSet ℓ) (B : CubicalSet ℓ') → Type (ℓ-max ℓ ℓ')
NaturalΣ A B = Σ[ f ∈ ((n : ℕ) → Cell A n → Cell B n) ] NaturalProof A B f

naturalToΣ : {A : CubicalSet ℓ} {B : CubicalSet ℓ'}
             → CubicalNatural A B → NaturalΣ A B
naturalToΣ f = mapCells f , λ m n u c → natural f u c

ΣToNatural : {A : CubicalSet ℓ} {B : CubicalSet ℓ'}
             → NaturalΣ A B → CubicalNatural A B
mapCells (ΣToNatural (f , p)) = f
natural (ΣToNatural (f , p)) {m} {n} = p m n

isSetCubicalNatural : {A : CubicalSet ℓ} {B : CubicalSet ℓ'}
                   → isSet (CubicalNatural A B)
isSetCubicalNatural {A = A} {B = B} =
  isSetRetract naturalToΣ ΣToNatural (λ f → cubicalNaturalExt (λ _ _ → refl))
    (isSetΣSndProp (isSetΠ2 (λ n _ → snd (cells B n)))
      (naturalProof-isProp A B))

CubicalSetCategory : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Category.ob (CubicalSetCategory ℓ) = CubicalSet ℓ
Category.Hom[_,_] (CubicalSetCategory ℓ) = CubicalNatural
Category.id (CubicalSetCategory ℓ) {x = A} = cubicalId A
Category._⋆_ (CubicalSetCategory ℓ) = _⋆n_
Category.⋆IdL (CubicalSetCategory ℓ) f = cubicalNaturalExt (λ _ _ → refl)
Category.⋆IdR (CubicalSetCategory ℓ) f = cubicalNaturalExt (λ _ _ → refl)
Category.⋆Assoc (CubicalSetCategory ℓ) f g h = cubicalNaturalExt (λ _ _ → refl)
Category.isSetHom (CubicalSetCategory ℓ) = isSetCubicalNatural

-- The all-dimensional graph cubical nerve.  This is N₁, not the Kan
-- replacement N∞ used by Carranza--Kapulkin under the name NG.
N₁ : Graph ℓ → CubicalSet ℓ
cells (N₁ G) n = Cube G n , isSetGraphHom
reindex (N₁ G) u c = c ∘g underlying u
reindex-id (N₁ G) c = rightIdentity c
reindex-compose (N₁ G) f g c = homExt (λ _ → refl)

N₁-map : {G : Graph ℓ} {H : Graph ℓ'} → Hom G H → CubicalNatural (N₁ G) (N₁ H)
mapCells (N₁-map f) n c = f ∘g c
natural (N₁-map f) u c = homExt (λ _ → refl)

N₁-map-id : (G : Graph ℓ) → N₁-map (idHom G) ≡ cubicalId (N₁ G)
N₁-map-id G = cubicalNaturalExt (λ n c → leftIdentity c)

N₁-map-compose : {G H K : Graph ℓ} (f : Hom G H) (g : Hom H K)
               → N₁-map (g ∘g f) ≡ N₁-map f ⋆n N₁-map g
N₁-map-compose f g = cubicalNaturalExt (λ n c → associativity g f c)

N₁-functor : (ℓ : Level) → Functor (GraphCategory ℓ) (CubicalSetCategory ℓ)
Functor.F-ob (N₁-functor ℓ) = N₁
Functor.F-hom (N₁-functor ℓ) = N₁-map
Functor.F-id (N₁-functor ℓ) {x = G} = N₁-map-id G
Functor.F-seq (N₁-functor ℓ) = N₁-map-compose

-- A representable n-cube and its checked Yoneda property.  A single
-- cell specifies the unique natural map out of the representable cube.
RepresentableCube : ℕ → CubicalSet ℓ-zero
cells (RepresentableCube n) m = CubicalMap m n , isSetCubicalMap
reindex (RepresentableCube n) f g = f ⋆c g
reindex-id (RepresentableCube n) g = Category.⋆IdL CubeCategory g
reindex-compose (RepresentableCube n) f g h = Category.⋆Assoc CubeCategory f g h

classifyCube : {n : ℕ} (A : CubicalSet ℓ) (c : Cell A n)
             → CubicalNatural (RepresentableCube n) A
mapCells (classifyCube A c) m u = reindex A u c
natural (classifyCube A c) f g = reindex-compose A f g c

classifier-evaluation : {n : ℕ} (A : CubicalSet ℓ) (c : Cell A n)
                     → mapCells (classifyCube A c) n (cubeId n) ≡ c
classifier-evaluation A c = reindex-id A c

every-natural-classified : {n : ℕ} (A : CubicalSet ℓ)
                          (η : CubicalNatural (RepresentableCube n) A)
                        → classifyCube A (mapCells η n (cubeId n)) ≡ η
every-natural-classified {n = n} A η = cubicalNaturalExt λ m u →
  sym (natural η u (cubeId n)) ∙ cong (mapCells η m) (Category.⋆IdR CubeCategory u)
