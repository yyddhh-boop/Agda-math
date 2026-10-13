{-# OPTIONS --cubical --safe #-}

module DHH.Enrichment.GraphHom where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.GraphSets
open import DHH.FiniteInterval using (UnitInterval)

private variable ℓG ℓH ℓK ℓL : Level

-- CK Def. 1.8 的 BOX 内 Hom：顶点是真正的图映射，边是逐点相邻。
-- 下方证明它恰好等价于原文 G BOX I₁ 上的一步柱同伦。
-- 无需有限性或枚举全部映射；每个输出值只对输入映射作求值。
HomGraph : Graph ℓG → Graph ℓH → Graph (ℓ-max ℓG ℓH)
Vertex (HomGraph G H) = Hom G H
vertex-isSet (HomGraph G H) = isSetGraphHom {G = G} {H = H}
Adj (HomGraph G H) f g = (x : Vertex G) → Adj H (onVertices f x) (onVertices g x)
adj-isProp (HomGraph G H) f g = isPropΠ (λ x → adj-isProp H _ _)
adj-refl (HomGraph G H) f x = adj-refl H (onVertices f x)
adj-sym (HomGraph G H) e x = adj-sym H (e x)

-- 闭结构的实际程序。K 方向相邻由 BOX 的第二分支给出，
-- G 方向相邻由第一分支给出；不存在“两坐标同时变化”的前提。
curryGraph : {K : Graph ℓK} {G : Graph ℓG} {H : Graph ℓH}
  → Hom (K BOX G) H → Hom K (HomGraph G H)
onVertices (onVertices (curryGraph h) k) x = onVertices h (k , x)
preserves (onVertices (curryGraph h) k) e = preserves h ∣ inl (refl , e) ∣₁
preserves (curryGraph h) e x = preserves h ∣ inr (e , refl) ∣₁

uncurryGraph : {K : Graph ℓK} {G : Graph ℓG} {H : Graph ℓH}
  → Hom K (HomGraph G H) → Hom (K BOX G) H
onVertices (uncurryGraph h) (k , x) = onVertices (onVertices h k) x
preserves (uncurryGraph {K = K} {G = G} {H = H} h)
  {x = (k , x)} {y = (l , y)} = PT.rec (adj-isProp H _ _) λ where
  (inl (e , a)) → subst (λ l' → Adj H (onVertices (onVertices h k) x)
    (onVertices (onVertices h l') y)) e (preserves (onVertices h k) a)
  (inr (a , e)) → subst (λ y' → Adj H (onVertices (onVertices h k) x)
    (onVertices (onVertices h l) y')) e (preserves h a x)

uncurry-curry : {K : Graph ℓK} {G : Graph ℓG} {H : Graph ℓH}
  (h : Hom (K BOX G) H) → uncurryGraph (curryGraph h) ≡ h
uncurry-curry h = homExt (λ _ → refl)

curry-uncurry : {K : Graph ℓK} {G : Graph ℓG} {H : Graph ℓH}
  (h : Hom K (HomGraph G H)) → curryGraph (uncurryGraph h) ≡ h
curry-uncurry h = homExt (λ _ → homExt (λ _ → refl))

boxHomIso : (K : Graph ℓK) (G : Graph ℓG) (H : Graph ℓH)
  → Iso (Hom (K BOX G) H) (Hom K (HomGraph G H))
Iso.fun (boxHomIso K G H) = curryGraph
Iso.inv (boxHomIso K G H) = uncurryGraph
Iso.rightInv (boxHomIso K G H) = curry-uncurry
Iso.leftInv (boxHomIso K G H) = uncurry-curry

boxHomEquivalence : (K : Graph ℓK) (G : Graph ℓG) (H : Graph ℓH)
  → Hom (K BOX G) H ≃ Hom K (HomGraph G H)
boxHomEquivalence K G H = isoToEquiv (boxHomIso K G H)

evaluationGraph : (G : Graph ℓG) (H : Graph ℓH)
  → Hom (HomGraph G H BOX G) H
evaluationGraph G H = uncurryGraph {K = HomGraph G H} {G = G} {H = H}
  (idHom (HomGraph G H))

boxSwap : (G : Graph ℓG) (H : Graph ℓH) → Hom (G BOX H) (H BOX G)
onVertices (boxSwap G H) (x , y) = y , x
preserves (boxSwap G H) = PT.rec (adj-isProp (H BOX G) _ _) λ where
  (inl (e , a)) → ∣ inr (a , e) ∣₁
  (inr (a , e)) → ∣ inl (e , a) ∣₁

-- 只有两种端点，故以下是 Bool 的构造子消去，不是大型组合枚举。
edgePath : {G : Graph ℓG} (x y : Vertex G) → Adj G x y → Hom UnitInterval G
onVertices (edgePath x y e) false = x
onVertices (edgePath x y e) true = y
preserves (edgePath {G = G} x y e) {false} {false} _ = adj-refl G x
preserves (edgePath {G = G} x y e) {false} {true} _ = e
preserves (edgePath {G = G} x y e) {true} {false} _ = adj-sym G e
preserves (edgePath {G = G} x y e) {true} {true} _ = adj-refl G y

record OneStepHomotopy {G : Graph ℓG} {H : Graph ℓH} (f g : Hom G H)
  : Type (ℓ-max ℓG ℓH) where
  field
    cylinderMap : Hom (G BOX UnitInterval) H
    startsAt : (x : Vertex G) → onVertices cylinderMap (x , false) ≡ onVertices f x
    endsAt : (x : Vertex G) → onVertices cylinderMap (x , true) ≡ onVertices g x
open OneStepHomotopy public

oneStepHomotopyExt : {G : Graph ℓG} {H : Graph ℓH} {f g : Hom G H}
  {p q : OneStepHomotopy f g} → cylinderMap p ≡ cylinderMap q → p ≡ q
cylinderMap (oneStepHomotopyExt e i) = e i
startsAt (oneStepHomotopyExt {H = H} {f = f} {p = p} {q = q} e i) x =
  isProp→PathP (λ j → vertex-isSet H (onVertices (e j) (x , false)) (onVertices f x))
    (startsAt p x) (startsAt q x) i
endsAt (oneStepHomotopyExt {H = H} {g = g} {p = p} {q = q} e i) x =
  isProp→PathP (λ j → vertex-isSet H (onVertices (e j) (x , true)) (onVertices g x))
    (endsAt p x) (endsAt q x) i

isPropOneStepHomotopy : {G : Graph ℓG} {H : Graph ℓH} (f g : Hom G H)
  → isProp (OneStepHomotopy f g)
isPropOneStepHomotopy f g p q = oneStepHomotopyExt (homExt λ where
  (x , false) → startsAt p x ∙ sym (startsAt q x)
  (x , true) → endsAt p x ∙ sym (endsAt q x))

edgeToOneStep : {G : Graph ℓG} {H : Graph ℓH} {f g : Hom G H}
  → Adj (HomGraph G H) f g → OneStepHomotopy f g
cylinderMap (edgeToOneStep {G = G} {H = H} {f} {g} e) =
  uncurryGraph {K = UnitInterval} {G = G} {H = H}
    (edgePath {G = HomGraph G H} f g e) ∘g boxSwap G UnitInterval
startsAt (edgeToOneStep e) x = refl
endsAt (edgeToOneStep e) x = refl

oneStepToEdge : {G : Graph ℓG} {H : Graph ℓH} {f g : Hom G H}
  → OneStepHomotopy f g → Adj (HomGraph G H) f g
oneStepToEdge {H = H} h x = subst2 (Adj H) (startsAt h x) (endsAt h x)
  (preserves (cylinderMap h) ∣ inl (refl , tt) ∣₁)

-- 柱的全部顶点已由两个端点图映射决定，边证明也是命题，
-- 所以一步同伦数据本身是命题；这里的等价甚至不需额外截断或选择。
edgeOneStepIso : {G : Graph ℓG} {H : Graph ℓH} (f g : Hom G H)
  → Iso (Adj (HomGraph G H) f g) (OneStepHomotopy f g)
Iso.fun (edgeOneStepIso f g) = edgeToOneStep
Iso.inv (edgeOneStepIso f g) = oneStepToEdge
Iso.rightInv (edgeOneStepIso f g) h = isPropOneStepHomotopy f g _ h
Iso.leftInv (edgeOneStepIso {G = G} {H = H} f g) e = adj-isProp (HomGraph G H) f g _ e

edgeOneStepEquivalence : {G : Graph ℓG} {H : Graph ℓH} (f g : Hom G H)
  → Adj (HomGraph G H) f g ≃ OneStepHomotopy f g
edgeOneStepEquivalence f g = isoToEquiv (edgeOneStepIso f g)

-- 复合逐点求值；在 BOX 边上只允许一个映射变化。
-- 逐点相邻一般不传递，不能把两次相邻擅自合成一条边。
compositionGraph : {G : Graph ℓG} {H : Graph ℓH} {K : Graph ℓK}
  → Hom (HomGraph H K BOX HomGraph G H) (HomGraph G K)
onVertices compositionGraph (g , f) = g ∘g f
preserves (compositionGraph {G = G} {H = H} {K = K})
  {x = (g , f)} {y = (g' , f')} = PT.rec (adj-isProp (HomGraph G K) (g ∘g f) (g' ∘g f')) λ where
  (inl (e , a)) → λ x → subst (λ h → Adj K (onVertices g (onVertices f x))
    (onVertices h (onVertices f' x))) e (preserves g (a x))
  (inr (a , e)) → λ x → subst (λ h → Adj K (onVertices g (onVertices f x))
    (onVertices g' (onVertices h x))) e (a (onVertices f x))

identityVertex : (G : Graph ℓG) → Vertex (HomGraph G G)
identityVertex = idHom

composition-left-unit : {G : Graph ℓG} {H : Graph ℓH} (f : Hom G H)
  → onVertices compositionGraph (identityVertex H , f) ≡ f
composition-left-unit = leftIdentity

composition-right-unit : {G : Graph ℓG} {H : Graph ℓH} (f : Hom G H)
  → onVertices compositionGraph (f , identityVertex G) ≡ f
composition-right-unit = rightIdentity

composition-associative : {G : Graph ℓG} {H : Graph ℓH} {K : Graph ℓK} {L : Graph ℓL}
  (h : Hom K L) (g : Hom H K) (f : Hom G H)
  → onVertices compositionGraph (onVertices compositionGraph (h , g) , f)
    ≡ onVertices compositionGraph (h , onVertices compositionGraph (g , f))
composition-associative h g f = homExt (λ _ → refl)

postcomposeGraph : {G : Graph ℓG} {H : Graph ℓH} {K : Graph ℓK}
  → Hom H K → Hom (HomGraph G H) (HomGraph G K)
onVertices (postcomposeGraph g) f = g ∘g f
preserves (postcomposeGraph g) e x = preserves g (e x)

precomposeGraph : {G : Graph ℓG} {H : Graph ℓH} {K : Graph ℓK}
  → Hom G H → Hom (HomGraph H K) (HomGraph G K)
onVertices (precomposeGraph f) g = g ∘g f
preserves (precomposeGraph f) e x = e (onVertices f x)

-- 这些是实际 BOX 闭结构及组合程序；没有断言相邻的可判定性，
-- 没有证明稳定神经 Kan，也没有将这里的 HomGraph 冒充 DK 局部化。
