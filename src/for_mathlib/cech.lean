import ..from_mathlib.category_theory.limits.kan_extension
import ..from_mathlib.category_theory.with_term
import algebraic_topology.simplicial_object

namespace simplicial_object

open category_theory
open category_theory.limits

open_locale simplicial

universes v u

variables (C : Type u) [category.{v} C]

-- TODO: Move this
instance : unique (simplex_category.truncated 0) :=
{ default := ⟨[0], by simp⟩,
  uniq := by tidy }

-- TODO: Golf + Move this
instance : unique (simplex_category.truncated 0)ᵒᵖ :=
{ default := opposite.op $ default _,
  uniq := λ a, begin
    have : a = opposite.op a.unop, by simp, rw this,
    apply opposite.unop_injective,
    simp,
  end }

@[derive category]
def augmented := (with_terminal simplex_category.{v}ᵒᵖ) ⥤ C

@[derive category]
def arr := with_terminal (discrete punit)

@[simps]
def arr.incl : arr.{v} ⥤ with_terminal simplex_category.{v}ᵒᵖ :=
  with_terminal.map $ discrete.functor $ λ _, default _

-- TODO: Make this functorial from `arrow C`? Prove equivalence?
def mk {X Y : C} (f : X ⟶ Y) : arr ⥤ C :=
with_terminal.lift (discrete.functor $ λ _, X) (λ _, f) (by tidy)

@[simps]
def to_arr : augmented C ⥤ (arr.{v} ⥤ C) := (whiskering_left _ _ _).obj arr.incl

-- TODO: unfold what it means for the Ran.diagram to have a limit.
noncomputable
def cech_nerve (f : arr.{v} ⥤ C)
  [∀ x : with_terminal (simplex_category.{v}ᵒᵖ), has_limit (Ran.diagram arr.incl f x)] :
  augmented C := Ran.loc arr.incl f

-- TODO: unfold what it means for C to have limits of this shape.
noncomputable
def cech [∀ x, has_limits_of_shape (structured_arrow x arr.incl) C] :
  (arr.{v} ⥤ C) ⥤ augmented C := Ran arr.incl

end simplicial_object
