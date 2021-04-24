import category_theory.limits.kan_extension
import category_theory.with_terminal
import algebraic_topology.simplicial_object
import category_theory.arrow
import category_theory.adjunction.limits
import .with_terminal
import .simplicial.augmented

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
--@[derive category]
--def augmented := (with_terminal simplex_category.{v}ᵒᵖ) ⥤ C

variable {C}

/--
The category of functors from `arr` to `C` is equivalent to `arrow C`.
-/
abbreviation arrow_diagram := with_terminal (discrete punit)

@[simps]
def arrow_diagram.incl : arrow_diagram.{v} ⥤ with_terminal simplex_category.{v}ᵒᵖ :=
  with_terminal.map $ discrete.functor $ λ _, (opposite.op [0])

def to_arrow : augmented C ⥤ arrow C :=
(whiskering_left _ _ _).obj arrow_diagram.incl ⋙ with_terminal.arrow_equiv.inverse

noncomputable
def cech [∀ x, has_limits_of_shape (structured_arrow x arrow_diagram.incl) C] :
  arrow C ⥤ augmented C :=
with_terminal.arrow_equiv.functor ⋙ Ran arrow_diagram.incl

noncomputable
def cech_adjunction [∀ x, has_limits_of_shape (structured_arrow x arrow_diagram.incl) C] :
  to_arrow ⊣ (cech : arrow C ⥤ _) :=
adjunction.comp _ _ (Ran.adjunction _ _) with_terminal.arrow_equiv.symm.to_adjunction

noncomputable
abbreviation cech_unit [∀ x, has_limits_of_shape (structured_arrow x arrow_diagram.incl) C]
  (M : augmented C) : M ⟶ cech.obj (to_arrow.obj M) := cech_adjunction.unit.app M

noncomputable
abbreviation cech_counit [∀ x, has_limits_of_shape (structured_arrow x arrow_diagram.incl) C]
  (M : arrow C) : to_arrow.obj (cech.obj M) ⟶ M := cech_adjunction.counit.app M

noncomputable
instance cech_preserves_limits [∀ x, has_limits_of_shape (structured_arrow x arrow_diagram.incl) C] :
  limits.preserves_limits (cech : arrow C ⥤ _) :=
adjunction.right_adjoint_preserves_limits cech_adjunction

end simplicial_object
