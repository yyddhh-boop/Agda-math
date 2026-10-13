{-# OPTIONS --cubical --safe #-}

module DHH.CubeCategory where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.GraphSets
open import DHH.Cubes

-- The concrete cube category WITH the two connections.  Only faces,
-- coordinate deletion, adjacent min/max, identities and their composites
-- occur.  Arbitrary graph maps Q m → Q n are deliberately NOT admitted.
-- Equality of morphisms is equality of the resulting vertex functions,
-- not equality of words: all cubical identities hold in this category.
data CubeWord : ℕ → ℕ → Type₀ where
  identityW : {n : ℕ} → CubeWord n n
  faceW : {n : ℕ} → Position (suc n) → Bool → CubeWord n (suc n)
  deleteW : {n : ℕ} → Position (suc n) → CubeWord (suc n) n
  minW maxW : {n : ℕ} → Position (suc n)
             → CubeWord (suc (suc n)) (suc n)
  composeW : {m n k : ℕ} → CubeWord m n → CubeWord n k → CubeWord m k

evaluate : {m n : ℕ} → CubeWord m n → Hom (Q m) (Q n)
evaluate identityW = idHom _
evaluate (faceW i b) = faceMap i b
evaluate (deleteW i) = deleteMap i
evaluate (minW i) = connectionMap i meetBool
evaluate (maxW i) = connectionMap i joinBool
evaluate (composeW f g) = evaluate g ∘g evaluate f

Generated : {m n : ℕ} → Hom (Q m) (Q n) → Type₀
Generated {m} {n} f = ∥ Σ[ w ∈ CubeWord m n ] evaluate w ≡ f ∥₁

record CubicalMap (m n : ℕ) : Type₀ where
  constructor cubicalMap
  field
    underlying : Hom (Q m) (Q n)
    generated : Generated {m = m} {n = n} underlying
open CubicalMap public

wordMap : {m n : ℕ} → CubeWord m n → CubicalMap m n
wordMap w = cubicalMap (evaluate w) ∣ w , refl ∣₁

cubeId : (n : ℕ) → CubicalMap n n
cubeId n = wordMap identityW

infixl 20 _⋆c_
_⋆c_ : {m n k : ℕ} → CubicalMap m n → CubicalMap n k → CubicalMap m k
underlying (f ⋆c g) = underlying g ∘g underlying f
generated (f ⋆c g) = PT.rec2 squash₁
  (λ { (u , p) (v , q) → ∣ composeW u v , cong₂ _∘g_ q p ∣₁ })
  (generated f) (generated g)

cubeMapExt : {m n : ℕ} {f g : CubicalMap m n}
           → underlying f ≡ underlying g → f ≡ g
underlying (cubeMapExt p i) = p i
generated (cubeMapExt {m = m} {n = n} {f = f} {g = g} p i) =
  isProp→PathP {B = λ j → Generated {m = m} {n = n} (p j)}
    (λ _ → squash₁) (generated f) (generated g) i

cubeMapToΣ : {m n : ℕ} → CubicalMap m n
           → Σ (Hom (Q m) (Q n)) (Generated {m = m} {n = n})
cubeMapToΣ f = underlying f , generated f

ΣToCubeMap : {m n : ℕ}
           → Σ (Hom (Q m) (Q n)) (Generated {m = m} {n = n}) → CubicalMap m n
ΣToCubeMap (f , p) = cubicalMap f p

isSetCubicalMap : {m n : ℕ} → isSet (CubicalMap m n)
isSetCubicalMap = isSetRetract cubeMapToΣ ΣToCubeMap
  (λ f → cubeMapExt refl) (isSetΣSndProp isSetGraphHom (λ _ → squash₁))

CubeCategory : Category ℓ-zero ℓ-zero
Category.ob CubeCategory = ℕ
Category.Hom[_,_] CubeCategory = CubicalMap
Category.id CubeCategory {x = n} = cubeId n
Category._⋆_ CubeCategory = _⋆c_
Category.⋆IdL CubeCategory f = cubeMapExt (rightIdentity (underlying f))
Category.⋆IdR CubeCategory f = cubeMapExt (leftIdentity (underlying f))
Category.⋆Assoc CubeCategory f g h =
  cubeMapExt (sym (associativity (underlying h) (underlying g) (underlying f)))
Category.isSetHom CubeCategory = isSetCubicalMap

cubeFace : {n : ℕ} → Position (suc n) → Bool → CubicalMap n (suc n)
cubeFace i b = wordMap (faceW i b)

cubeDelete : {n : ℕ} → Position (suc n) → CubicalMap (suc n) n
cubeDelete i = wordMap (deleteW i)

cubeMin cubeMax : {n : ℕ} → Position (suc n)
                → CubicalMap (suc (suc n)) (suc n)
cubeMin i = wordMap (minW i)
cubeMax i = wordMap (maxW i)
