import category_theory.limits.cones
import algebraic_topology.simplicial_object
import .fan

namespace simplicial_object

local attribute [tidy] tactic.case_bash

open category_theory

universes v u

variables {C : Type u} [category.{v} C] {X B : C} (f : X ⟶ B)

abbreviation ufin (n : ℕ) := ulift.{v} (fin n)
abbreviation ufin.map {m n : ℕ} (h : fin m → fin n) : ufin m → ufin n :=
  λ ⟨i⟩, ulift.up (h i)

abbreviation Cech_diagram (a : simplex_category.{v}) : fan (ufin (a.len+1)) ⥤ C :=
fan.mk (λ i, X) (λ i, f)

def Cech.map_cone {a b : simplex_category.{v}ᵒᵖ} (h : a ⟶ b)
  (C : limits.cone (Cech_diagram f a.unop)) : limits.cone (Cech_diagram f b.unop) := sorry

end simplicial_object
