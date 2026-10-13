{-# OPTIONS --cubical --safe #-}

module DHH.Cubes where

open import Cubical.Foundations.Prelude hiding (Cube; lower)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Unit using (Unit; tt; isSetUnit; isPropUnit)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT

open import DHH.Graph
open import DHH.FiniteInterval using (UnitInterval)

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Finite discrete coordinate positions.  Neither these positions nor
-- their Bool coordinates are the built-in Cubical Agda interval I.
data Position : ℕ → Type₀ where
  here  : {n : ℕ} → Position (suc n)
  there : {n : ℕ} → Position n → Position (suc n)

weakenPosition : {n : ℕ} → Position n → Position (suc n)
weakenPosition here = here
weakenPosition (there i) = there (weakenPosition i)

PointGraph : Graph ℓ-zero
Vertex PointGraph = Unit
vertex-isSet PointGraph = isSetUnit
Adj PointGraph _ _ = Unit
adj-isProp PointGraph _ _ = isPropUnit
adj-refl PointGraph _ = tt
adj-sym PointGraph _ = tt

-- 构造视角：Q 按维数 n 递归；0 给单点，每一步加一个 BOX 因子。
-- 给定维数可展开此有限表达式；Cube G n 则是图映射类型，未枚举其中元素。
Q : ℕ → Graph ℓ-zero
Q zero = PointGraph
Q (suc n) = UnitInterval BOX Q n

Cube : Graph ℓ → ℕ → Type ℓ
Cube G n = Hom (Q n) G

-- Cartesian products of graph maps preserve BOX adjacency.
boxHom : {G : Graph ℓ} {H : Graph ℓ'}
         {K : Graph ℓ''} {L : Graph ℓ''}
       → Hom G K → Hom H L → Hom (G BOX H) (K BOX L)
onVertices (boxHom f g) (x , y) = onVertices f x , onVertices g y
preserves (boxHom {K = K} {L = L} f g) =
  PT.rec (adj-isProp (K BOX L) _ _) λ where
    (inl (p , e)) → ∣ inl (cong (onVertices f) p , preserves g e) ∣₁
    (inr (e , p)) → ∣ inr (preserves f e , cong (onVertices g) p) ∣₁

insert : {n : ℕ} → Position (suc n) → Bool
       → Vertex (Q n) → Vertex (Q (suc n))
insert here b x = b , x
insert {n = suc n} (there i) b (a , x) = a , insert i b x

delete : {n : ℕ} → Position (suc n)
       → Vertex (Q (suc n)) → Vertex (Q n)
delete here (b , x) = x
delete {n = suc n} (there i) (a , x) = a , delete i x

faceMap : {n : ℕ} → Position (suc n) → Bool
        → Hom (Q n) (Q (suc n))
onVertices (faceMap i b) = insert i b
preserves (faceMap here b) e = ∣ inl (refl , e) ∣₁
preserves (faceMap {n = suc n} (there i) b) e =
  preserves (boxHom (idHom UnitInterval) (faceMap i b)) e

deleteMap : {n : ℕ} → Position (suc n)
          → Hom (Q (suc n)) (Q n)
onVertices (deleteMap i) = delete i
preserves (deleteMap {n = n} here) {x = (a , u)} {y = (b , v)} =
  PT.rec (adj-isProp (Q n) u v) λ where
    (inl (p , e)) → e
    (inr (e , p)) → subst (Adj (Q n) u) p (adj-refl (Q n) u)
preserves (deleteMap {n = suc n} (there i)) e =
  preserves (boxHom (idHom UnitInterval) (deleteMap i)) e

face : {G : Graph ℓ} {n : ℕ} → Position (suc n) → Bool
     → Cube G (suc n) → Cube G n
face i b c = c ∘g faceMap i b

degeneracy : {G : Graph ℓ} {n : ℕ} → Position (suc n)
           → Cube G n → Cube G (suc n)
degeneracy i c = c ∘g deleteMap i

-- A face of a degeneracy in the repeated coordinate is the original
-- cube, for every dimension and every coordinate.
-- 证明视角：对位置 i 结构归纳。here 是基例；there 去掉一个前缀坐标。
-- 相同递归同时控制操作和证明，因此覆盖任意维数，不依赖逐维测试。
delete-insert : {n : ℕ} (i : Position (suc n)) (b : Bool)
                (x : Vertex (Q n)) → delete i (insert i b x) ≡ x
delete-insert here b x = refl
delete-insert {n = suc n} (there i) b (a , x) =
  cong (λ y → a , y) (delete-insert i b x)

face-of-degeneracy : {G : Graph ℓ} {n : ℕ}
                     (i : Position (suc n)) (b : Bool) (c : Cube G n)
                   → face i b (degeneracy i c) ≡ c
face-of-degeneracy i b c =
  homExt (λ x → cong (onVertices c) (delete-insert i b x))

-- Adjacent-coordinate face and degeneracy identities, with arbitrary
-- prefix length.  This file does not claim to prove every cubical law.
insert-twice : {n : ℕ} (i : Position (suc n)) (a b : Bool)
               (x : Vertex (Q n))
             → insert (weakenPosition i) a (insert i b x)
             ≡ insert (there i) b (insert i a x)
insert-twice here a b x = refl
insert-twice {n = suc n} (there i) a b (c , x) =
  cong (λ y → c , y) (insert-twice i a b x)

adjacent-faces : {G : Graph ℓ} {n : ℕ}
                 (i : Position (suc n)) (a b : Bool)
                 (c : Cube G (suc (suc n)))
               → face i b (face (weakenPosition i) a c)
               ≡ face i a (face (there i) b c)
adjacent-faces i a b c =
  homExt (λ x → cong (onVertices c) (insert-twice i a b x))

delete-twice : {n : ℕ} (i : Position (suc n))
               (x : Vertex (Q (suc (suc n))))
             → delete i (delete (weakenPosition i) x)
             ≡ delete i (delete (there i) x)
delete-twice here (a , b , x) = refl
delete-twice {n = suc n} (there i) (a , x) =
  cong (λ y → a , y) (delete-twice i x)

adjacent-degeneracies : {G : Graph ℓ} {n : ℕ}
                        (i : Position (suc n)) (c : Cube G n)
                      → degeneracy (weakenPosition i) (degeneracy i c)
                      ≡ degeneracy (there i) (degeneracy i c)
adjacent-degeneracies i c =
  homExt (λ x → cong (onVertices c) (delete-twice i x))

-- Connections merge two adjacent coordinates by min or max.  They
-- are graph maps because the unit interval graph is complete.
meetBool : Bool → Bool → Bool
meetBool false b = false
meetBool true b = b

joinBool : Bool → Bool → Bool
joinBool false b = b
joinBool true b = true

merge : {n : ℕ} → Position (suc n) → (Bool → Bool → Bool)
      → Vertex (Q (suc (suc n))) → Vertex (Q (suc n))
merge here op (a , b , x) = op a b , x
merge {n = suc n} (there i) op (a , x) = a , merge i op x

connectionMap : {n : ℕ} → Position (suc n) → (Bool → Bool → Bool)
              → Hom (Q (suc (suc n))) (Q (suc n))
onVertices (connectionMap i op) = merge i op
preserves (connectionMap {n = n} here op)
  {x = (a , b , u)} {y = (a' , b' , v)} =
  PT.rec (adj-isProp (Q (suc n)) _ _) λ where
    (inl (p , e)) → PT.rec (adj-isProp (Q (suc n)) _ _)
      (λ where
        (inl (q , e')) → ∣ inl (cong₂ op p q , e') ∣₁
        (inr (e' , q)) → ∣ inr (tt , q) ∣₁) e
    (inr (e , p)) → ∣ inr (tt , cong snd p) ∣₁
preserves (connectionMap {n = suc n} (there i) op) e =
  preserves (boxHom (idHom UnitInterval) (connectionMap i op)) e

connection : {G : Graph ℓ} {n : ℕ} → Position (suc n)
           → (Bool → Bool → Bool) → Cube G (suc n)
           → Cube G (suc (suc n))
connection i op c = c ∘g connectionMap i op

merge-insert-unit : {n : ℕ} (i : Position (suc n))
                    (op : Bool → Bool → Bool) (b : Bool)
                  → ((a : Bool) → op b a ≡ a)
                  → (x : Vertex (Q (suc n)))
                  → merge i op (insert (weakenPosition i) b x) ≡ x
merge-insert-unit here op b unit (a , x) =
  cong (λ y → y , x) (unit a)
merge-insert-unit {n = suc n} (there i) op b unit (a , x) =
  cong (λ y → a , y) (merge-insert-unit i op b unit x)

face-of-min-connection : {G : Graph ℓ} {n : ℕ}
                         (i : Position (suc n)) (c : Cube G (suc n))
                       → face (weakenPosition i) true
                           (connection i meetBool c) ≡ c
face-of-min-connection i c = homExt λ x →
  cong (onVertices c) (merge-insert-unit i meetBool true (λ a → refl) x)

face-of-max-connection : {G : Graph ℓ} {n : ℕ}
                         (i : Position (suc n)) (c : Cube G (suc n))
                       → face (weakenPosition i) false
                           (connection i joinBool c) ≡ c
face-of-max-connection i c = homExt λ x →
  cong (onVertices c) (merge-insert-unit i joinBool false (λ a → refl) x)

-- Covariance in the graph: postcompose every cube by a graph map.
nerveMap : {G : Graph ℓ} {H : Graph ℓ'} {n : ℕ}
         → Hom G H → Cube G n → Cube H n
nerveMap f c = f ∘g c

nerveMap-identity : {G : Graph ℓ} {n : ℕ} (c : Cube G n)
                  → nerveMap {n = n} (idHom G) c ≡ c
nerveMap-identity c = homExt (λ _ → refl)

nerveMap-composition : {G : Graph ℓ} {H : Graph ℓ'} {K : Graph ℓ''}
                       {n : ℕ} (g : Hom H K) (f : Hom G H)
                       (c : Cube G n)
                     → nerveMap {n = n} (g ∘g f) c
                     ≡ nerveMap {n = n} g (nerveMap {n = n} f c)
nerveMap-composition g f c = homExt (λ _ → refl)

nerveMap-face : {G : Graph ℓ} {H : Graph ℓ'} {n : ℕ}
                (f : Hom G H) (i : Position (suc n)) (b : Bool)
                (c : Cube G (suc n))
              → nerveMap {n = n} f (face i b c)
              ≡ face i b (nerveMap {n = suc n} f c)
nerveMap-face f i b c = homExt (λ _ → refl)

nerveMap-degeneracy : {G : Graph ℓ} {H : Graph ℓ'} {n : ℕ}
                      (f : Hom G H) (i : Position (suc n)) (c : Cube G n)
                    → nerveMap {n = suc n} f (degeneracy i c)
                    ≡ degeneracy i (nerveMap {n = n} f c)
nerveMap-degeneracy f i c = homExt (λ _ → refl)

nerveMap-connection : {G : Graph ℓ} {H : Graph ℓ'} {n : ℕ}
                      (f : Hom G H) (i : Position (suc n))
                      (op : Bool → Bool → Bool) (c : Cube G (suc n))
                    → nerveMap {n = suc (suc n)} f (connection i op c)
                    ≡ connection i op (nerveMap {n = suc n} f c)
nerveMap-connection f i op c = homExt (λ _ → refl)

-- An ordered pair of distinct coordinates in an (n+2)-cube.  `front j`
-- puts the first coordinate at the front and the second at j+1;
-- `under` adds an arbitrary common prefix.  Thus j can also specify
-- nonadjacent coordinates, not only the adjacent case checked above.
data CoordinatePair : ℕ → Type₀ where
  front : {n : ℕ} → Position (suc n) → CoordinatePair n
  under : {n : ℕ} → CoordinatePair n → CoordinatePair (suc n)

lower upper : {n : ℕ} → CoordinatePair n → Position (suc n)
lower (front j) = here
lower (under p) = there (lower p)
upper (front j) = j
upper (under p) = there (upper p)

lowerWide upperWide : {n : ℕ} → CoordinatePair n
                    → Position (suc (suc n))
lowerWide (front j) = here
lowerWide (under p) = there (lowerWide p)
upperWide (front j) = there j
upperWide (under p) = there (upperWide p)

insert-distinct : {n : ℕ} (p : CoordinatePair n) (a b : Bool)
                  (x : Vertex (Q n))
                → insert (lowerWide p) a (insert (upper p) b x)
                ≡ insert (upperWide p) b (insert (lower p) a x)
insert-distinct (front j) a b x = refl
insert-distinct (under p) a b (c , x) =
  cong (λ y → c , y) (insert-distinct p a b x)

faces-commute : {G : Graph ℓ} {n : ℕ} (p : CoordinatePair n)
                (a b : Bool) (c : Cube G (suc (suc n)))
              → face (upper p) b (face (lowerWide p) a c)
              ≡ face (lower p) a (face (upperWide p) b c)
faces-commute p a b c = homExt λ x →
  cong (onVertices c) (insert-distinct p a b x)

delete-distinct : {n : ℕ} (p : CoordinatePair n)
                  (x : Vertex (Q (suc (suc n))))
                → delete (upper p) (delete (lowerWide p) x)
                ≡ delete (lower p) (delete (upperWide p) x)
delete-distinct (front j) (a , x) = refl
delete-distinct (under p) (a , x) =
  cong (λ y → a , y) (delete-distinct p x)

degeneracies-commute : {G : Graph ℓ} {n : ℕ} (p : CoordinatePair n)
                       (c : Cube G n)
                     → degeneracy (lowerWide p) (degeneracy (upper p) c)
                     ≡ degeneracy (upperWide p) (degeneracy (lower p) c)
degeneracies-commute p c = homExt λ x →
  cong (onVertices c) (delete-distinct p x)

delete-insert-upper : {n : ℕ} (p : CoordinatePair n) (b : Bool)
                      (x : Vertex (Q (suc n)))
                    → delete (lowerWide p) (insert (upperWide p) b x)
                    ≡ insert (upper p) b (delete (lower p) x)
delete-insert-upper (front j) b (a , x) = refl
delete-insert-upper (under p) b (a , x) =
  cong (λ y → a , y) (delete-insert-upper p b x)

delete-insert-lower : {n : ℕ} (p : CoordinatePair n) (a : Bool)
                      (x : Vertex (Q (suc n)))
                    → delete (upperWide p) (insert (lowerWide p) a x)
                    ≡ insert (lower p) a (delete (upper p) x)
delete-insert-lower (front j) a x = refl
delete-insert-lower (under p) a (b , x) =
  cong (λ y → b , y) (delete-insert-lower p a x)

face-degeneracy-upper : {G : Graph ℓ} {n : ℕ} (p : CoordinatePair n)
                        (b : Bool) (c : Cube G (suc n))
                      → face (upperWide p) b (degeneracy (lowerWide p) c)
                      ≡ degeneracy (lower p) (face (upper p) b c)
face-degeneracy-upper p b c = homExt λ x →
  cong (onVertices c) (delete-insert-upper p b x)

face-degeneracy-lower : {G : Graph ℓ} {n : ℕ} (p : CoordinatePair n)
                        (a : Bool) (c : Cube G (suc n))
                      → face (lowerWide p) a (degeneracy (upperWide p) c)
                      ≡ degeneracy (upper p) (face (lower p) a c)
face-degeneracy-lower p a c = homExt λ x →
  cong (onVertices c) (delete-insert-lower p a x)
