import category_theory.limits.kan_extension
import category_theory.with_terminal
import algebraic_topology.simplicial_object
import category_theory.arrow
import .with_terminal

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

/--
Augmented simplicial objects.
-/
@[derive category]
def augmented := (with_terminal simplex_category.{v}ᵒᵖ) ⥤ C

variable {C}

/--
The category of functors from `arr` to `C` is equivalent to `arrow C`.
-/
@[derive category]
abbreviation arrow_diagram := with_terminal (discrete punit)

@[simps]
def arrow_diagram.incl : arrow_diagram.{v} ⥤ with_terminal simplex_category.{v}ᵒᵖ :=
  with_terminal.map $ discrete.functor $ λ _, default _

def to_arrow : augmented C ⥤ arrow C :=
(whiskering_left _ _ _).obj arrow_diagram.incl ⋙ with_terminal.arrow_equiv.inverse

noncomputable
def cech [∀ x, has_limits_of_shape (structured_arrow x arrow_diagram.incl) C] :
  arrow C ⥤ augmented C :=
with_terminal.arrow_equiv.functor ⋙ Ran arrow_diagram.incl

noncomputable
def adjunction [∀ x, has_limits_of_shape (structured_arrow x arrow_diagram.incl) C] :
  to_arrow ⊣ (cech : arrow C ⥤ _) :=
adjunction.comp _ _ (Ran.adjunction _ _) with_terminal.arrow_equiv.symm.to_adjunction

/-
/-- Make a functor from `arr` to `C` associated to an arrow. -/
def arr_mk {X Y : C} (f : X ⟶ Y) : arrow_diagram ⥤ C :=
with_terminal.lift (discrete.functor $ λ _, X) (λ _, f) (by tidy)

@[simps]
def to_arrow : augmented C ⥤ (arrow_diagram.{v} ⥤ C) :=
(whiskering_left _ _ _).obj arrow_diagram.incl

-- TODO: unfold what it means for the Ran.diagram to have a limit.
noncomputable
def cech_nerve {X Y : C} (f : X ⟶ Y)
  [∀ x : with_terminal (simplex_category.{v}ᵒᵖ),
    has_limit (Ran.diagram arrow_diagram.incl (arr_mk f) x)] :
  augmented C := Ran.loc arrow_diagram.incl (arr_mk f)

-- TODO: unfold what it means for C to have limits of this shape.
-- TODO: Replace `arrow_diagram ⥤ C` with `arrow C` when we have the equivalence mentioned above?
noncomputable
def cech [∀ x, has_limits_of_shape (structured_arrow x arrow_diagram.incl) C] :
  (arrow_diagram.{v} ⥤ C) ⥤ augmented C := Ran arrow_diagram.incl
-/

end simplicial_object
