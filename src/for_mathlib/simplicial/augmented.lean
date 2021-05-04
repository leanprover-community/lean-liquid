import category_theory.arrow
import category_theory.with_terminal
import algebraic_topology.simplicial_object

/-!
This file defines augmented (co)simplicial objects, and develops a basic API.
-/

open category_theory

open_locale simplicial

universes v u

variables (C : Type u) [category.{v} C]

namespace simplicial_object

/-- Augmented simplicial objects. -/
@[derive category]
def augmented := (with_terminal simplex_category.{v}ᵒᵖ) ⥤ C

namespace augmented

variable {C}

/-- The forgetful functor from augmented simplicial objects to simplicial objects. -/
def drop : augmented C ⥤ simplicial_object C :=
(whiskering_left _ _ _).obj with_terminal.incl

/-- The functor sending an augmented object to the augmentation map. -/
def to_arrow : augmented C ⥤ arrow C :=
{ obj := λ M, M.map $ with_terminal.hom_from $ opposite.op [0],
  map := λ M N f,
  { left := f.app _,
    right := f.app _,
    w' := by {erw f.naturality, refl} } }

@[simp]
lemma hom_eq {M : augmented C} {x : simplex_categoryᵒᵖ} (f : x ⟶ opposite.op [0]) :
  (drop.obj M).map f ≫ (to_arrow.obj M).hom = M.map (with_terminal.hom_from _) :=
by {erw ← M.map_comp, simp}

end augmented

end simplicial_object

/-- Cosimplicial objects. -/
@[derive category]
def cosimplicial_object := simplex_category.{v} ⥤ C

namespace cosimplicial_object


/-- Augmented cosimplicial objects. -/
@[derive category]
def augmented := (with_initial simplex_category.{v}) ⥤ C

variable {C}

abbreviation const : C ⥤ cosimplicial_object C := category_theory.functor.const _

namespace augmented

/-- The forgetful functor from augmented cosimplicial objects to simplicial objects. -/
def drop : augmented C ⥤ cosimplicial_object C :=
(whiskering_left _ _ _).obj with_initial.incl

/-- The functor sending an augmented object to the augmentation map. -/
def to_arrow : augmented C ⥤ arrow C :=
{ obj := λ M, M.map $ with_initial.hom_to $ [0],
  map := λ M N f,
  { left := f.app _,
    right := f.app _,
    w' := by {erw f.naturality, refl} } }

@[simp]
lemma hom_eq {M : augmented C} {x : simplex_category} (f : [0] ⟶ x) :
  (to_arrow.obj M).hom ≫ (drop.obj M).map f = M.map (with_initial.hom_to _) :=
by {erw ← M.map_comp, simp}

end augmented

end cosimplicial_object
