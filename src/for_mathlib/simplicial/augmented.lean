import category_theory.comma
import algebraic_topology.simplicial_object

/-!
This file defines augmented (co)simplicial objects, and develops a basic API.
-/

open category_theory

open_locale simplicial

universes v u

variables (C : Type u) [category.{v} C]

namespace simplicial_object

variable {C}
@[simps]
def const : C ⥤ simplicial_object C := category_theory.functor.const _
variable (C)

/-- Augmented simplicial objects. -/
@[derive category]
def augmented := comma (𝟭 (simplicial_object C)) const

variable {C}

namespace augmented

@[simps]
def drop : augmented C ⥤ simplicial_object C := comma.fst _ _

@[simps]
def point : augmented C ⥤ C := comma.snd _ _

end augmented

end simplicial_object

/-- Cosimplicial objects. -/
@[derive category]
def cosimplicial_object := simplex_category.{v} ⥤ C

namespace cosimplicial_object

variable {C}
@[simps]
def const : C ⥤ cosimplicial_object C := category_theory.functor.const _
variable (C)

/-- Augmented cosimplicial objects. -/
@[derive category]
def augmented := comma const (𝟭 (cosimplicial_object C))

variable {C}

namespace augmented

/-- The forgetful functor from augmented cosimplicial objects to simplicial objects. -/
@[simps]
def drop : augmented C ⥤ cosimplicial_object C := comma.snd _ _

@[simps]
def point : augmented C ⥤ C := comma.fst _ _

end augmented

end cosimplicial_object
