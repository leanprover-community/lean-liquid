import category_theory.limits.shapes.wide_pullbacks
--import category_theory.over
import algebraic_topology.simplicial_object
import category_theory.products.basic
import category_theory.arrow
import for_mathlib.simplicial.constant

noncomputable theory

namespace category_theory
open category_theory.limits

universes v u

variables {C : Type u} [category.{v} C]

namespace limits
-- TODO: Move this! (or just make a mathlib PR!)

abbreviation has_wide_pullback {J : Type v} (B : C) (objs : J → C)
  (arrows : Π (j : J), objs j ⟶ B) := has_limit (wide_pullback_shape.wide_cospan B objs arrows)

abbreviation wide_pullback {J : Type v} (B : C) (objs : J → C) (arrows : Π (j : J), objs j ⟶ B)
  [has_wide_pullback B objs arrows] : C :=
limit (wide_pullback_shape.wide_cospan B objs arrows)

abbreviation wide_pullback.π {J : Type v} {B : C} {objs : J → C} {arrows : Π (j : J), objs j ⟶ B}
  [has_wide_pullback B objs arrows] (j : J) : wide_pullback B objs arrows ⟶ objs j :=
limit.π (wide_pullback_shape.wide_cospan B objs arrows) (option.some j)

abbreviation wide_pullback.base {J : Type v} {B : C} {objs : J → C} {arrows : Π (j : J), objs j ⟶ B}
  [has_wide_pullback B objs arrows] : wide_pullback B objs arrows ⟶ B :=
limit.π (wide_pullback_shape.wide_cospan B objs arrows) option.none

@[simp]
lemma wide_pullback.π_base {J : Type v} {B : C} {objs : J → C} {arrows : Π (j : J), objs j ⟶ B}
  [has_wide_pullback B objs arrows] (j : J) :
  (wide_pullback.π j : wide_pullback B objs arrows ⟶ _) ≫ arrows j = wide_pullback.base :=
by apply (limit.cone (wide_pullback_shape.wide_cospan B objs arrows)).w (wide_pullback_shape.hom.term j)

abbreviation wide_pullback.lift {J : Type v} {B : C} {objs : J → C} {arrows : Π (j : J), objs j ⟶ B}
  [has_wide_pullback B objs arrows] {X : C} (f : X ⟶ B) (π : Π (j : J), X ⟶ objs j)
  (w : ∀ j, π j ≫ arrows j = f) : X ⟶ wide_pullback B objs arrows :=
limit.lift (wide_pullback_shape.wide_cospan B objs arrows)
  (wide_pullback_shape.mk_cone f π (by convert w))

@[simp]
lemma wide_pullback.lift_π {J : Type v} {B : C} {objs : J → C} {arrows : Π (j : J), objs j ⟶ B}
  [has_wide_pullback B objs arrows] {X : C} (f : X ⟶ B) (π : Π (j : J), X ⟶ objs j)
  (w : ∀ j, π j ≫ arrows j = f) (j : J) : wide_pullback.lift f π w ≫ wide_pullback.π j = π j :=
(limit.is_limit (wide_pullback_shape.wide_cospan B objs arrows)).fac _ _

@[simp]
lemma wide_pullback.lift_base {J : Type v} {B : C} {objs : J → C} {arrows : Π (j : J), objs j ⟶ B}
  [has_wide_pullback B objs arrows] {X : C} (f : X ⟶ B) (π : Π (j : J), X ⟶ objs j)
  (w : ∀ j, π j ≫ arrows j = f) : wide_pullback.lift f π w ≫ wide_pullback.base = f :=
(limit.is_limit (wide_pullback_shape.wide_cospan B objs arrows)).fac _ _

--@[ext]
lemma wide_pullback.hom_eq_lift {J : Type v} {B : C} {objs : J → C} {arrows : Π (j : J), objs j ⟶ B}
  [has_wide_pullback B objs arrows] {X : C} (f : X ⟶ B) (π : Π (j : J), X ⟶ objs j)
  (w : ∀ j, π j ≫ arrows j = f) (g : X ⟶ wide_pullback B objs arrows) :
  (∀ j : J, g ≫ wide_pullback.π j = π j) → g ≫ wide_pullback.base = f → wide_pullback.lift f π w = g :=
begin
  intros h1 h2,
  symmetry,
  apply (limit.is_limit (wide_pullback_shape.wide_cospan B objs arrows)).uniq
    (wide_pullback_shape.mk_cone f π (by convert w)) g,
  rintro (j|j),
  exact h2,
  exact h1 _,
end

lemma wide_pullback.eq_lift {J : Type v} {B : C} {objs : J → C} {arrows : Π (j : J), objs j ⟶ B}
  [has_wide_pullback B objs arrows] {X : C} (f : X ⟶ wide_pullback B objs arrows) :
  f = wide_pullback.lift (f ≫ wide_pullback.base) (λ j, f ≫ wide_pullback.π _) (by tidy) :=
by {symmetry, apply wide_pullback.hom_eq_lift, tidy}

@[ext]
lemma wide_pullback.hom_ext {J : Type v} {B : C} {objs : J → C} {arrows : Π (j : J), objs j ⟶ B}
  [has_wide_pullback B objs arrows] {X : C} (f g : X ⟶ wide_pullback B objs arrows) :
  (∀ j : J, f ≫ wide_pullback.π j = g ≫ wide_pullback.π j) →
  f ≫ wide_pullback.base = g ≫ wide_pullback.base → f = g :=
begin
  intros h1 h2,
  rw wide_pullback.eq_lift f,
  apply wide_pullback.hom_eq_lift,
  tidy,
end

end limits

abbreviation ufin (n : ℕ) := ulift (fin n)
abbreviation ufin.up {n} : fin n → ufin n := _root_.ulift.up
abbreviation ufin.map {m n} (f : fin m → fin n) : ufin m → ufin n :=
λ i, ufin.up $ f i.down
abbreviation ufin.succ {n} : ufin n → ufin (n+1) := ufin.map fin.succ

instance {n} : has_zero (ufin (n+1)) := ⟨ufin.up 0⟩

abbreviation ufin.pred {n} (x : ufin (n+1)) (hx : x ≠ 0) : ufin n :=
ufin.up $ fin.pred x.down (λ c, hx $ equiv.ulift.injective c)

--local attribute [semireducible] simplex_category.hom

@[simps]
def cech_obj {X B : C} (f : X ⟶ B)
  [∀ (n : ℕ), limits.has_wide_pullback B (λ (i : ufin (n+1)), X) (λ i, f)] :
  simplicial_object C :=
{ obj := λ x, limits.wide_pullback B (λ (i : ufin (x.unop.len+1)), X) (λ i, f),
  map := λ x y g, limits.wide_pullback.lift limits.wide_pullback.base
    (λ i, limits.wide_pullback.π $ ufin.map g.unop.to_preorder_hom i) (by simp) }.

-- tidy gets map_id' and map_comp', but it needs a bit of help due to deterministic timeouts :-(
@[simps]
def cech [∀ (n : ℕ) (B X : C) (f : X ⟶ B), limits.has_wide_pullback B (λ i : ufin (n+1), X) (λ i, f)] :
  arrow C ⥤ simplicial_object C :=
{ obj := λ F, cech_obj F.hom,
  map := λ F G ff,
  { app := λ x, limits.wide_pullback.lift (limits.wide_pullback.base ≫ ff.right)
      (λ i, limits.wide_pullback.π i ≫ ff.left) (by {intros i, simp [← category.assoc]}) },
  map_id' := begin
    intros f,
    ext1,
    ext1 j,
    apply limits.wide_pullback.hom_ext,
    tidy,
  end,
  map_comp' := begin
    intros x y z f g,
    ext1,
    ext1 j,
    apply limits.wide_pullback.hom_ext,
    { intros i,
      simp [wide_pullback_shape.mk_cone] },
    { simp [wide_pullback_shape.mk_cone] }
  end }.

namespace cech

def augmentation [∀ (n : ℕ) (B X : C) (f : X ⟶ B), limits.has_wide_pullback B (λ i : ufin (n+1), X) (λ i, f)]
  (F : arrow C) : cech.obj F ⟶ simplicial_object.const.obj F.right := { app := λ x, limits.wide_pullback.base }

end cech

end category_theory
