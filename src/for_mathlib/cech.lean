import category_theory.limits.cones
import algebraic_topology.simplicial_object
import .fan

noncomputable theory

namespace simplicial_object

local attribute [tidy] tactic.case_bash

open category_theory

universes v u

variables {C : Type u} [category.{v} C] {X B : C} (f : X ⟶ B)

abbreviation ufin (n : ℕ) := ulift.{v} (fin n)
abbreviation ufin.map {m n : ℕ} (h : fin m → fin n) : ufin m → ufin n :=
  λ i, ulift.up (h i.down)

abbreviation Cech.diagram (a : simplex_category.{v}) : fan (ufin.{v} (a.len+1)) ⥤ C :=
fan.mk (λ i, X) (λ i, f)

abbreviation Cech.map_cone {a b : simplex_category.{v}ᵒᵖ} (h : a ⟶ b)
  (CC : limits.cone (Cech.diagram f a.unop)) : limits.cone (Cech.diagram f b.unop) :=
fan.map_cone (ufin.map h.unop.to_preorder_hom) _ _ CC

abbreviation Cech.obj_aux [limits.has_limits C] (a : simplex_category.{v}ᵒᵖ) : C :=
limits.limit (Cech.diagram f a.unop)

abbreviation Cech.map_aux [limits.has_limits C] {a b : simplex_category.{v}ᵒᵖ} (h : a ⟶ b) :
  Cech.obj_aux f a ⟶ Cech.obj_aux f b :=
limits.limit.lift (Cech.diagram f b.unop) (Cech.map_cone _ h _)

def Cech [limits.has_limits C] : simplicial_object C :=
{ obj := λ a, Cech.obj_aux f a,
  map := λ a b g, Cech.map_aux f g,
  map_comp' := begin
    intros x y z f g,
    delta Cech.map_aux Cech.map_cone Cech.diagram,
    ext ⟨j|j⟩,
    { delta fan.map_cone, tidy },
    { delta fan.map_cone, tidy }
  end }.

end simplicial_object
