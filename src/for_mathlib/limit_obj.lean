import category_theory.limits.functor_category

namespace category_theory.limits

open category_theory

universes w v u
variables {C : Type (max v u)} [category.{v} C]
variables {D : Type w} [category.{max v u} D]
variables {J : Type (max v u)} [small_category J]

noncomputable
def limit_obj_iso [has_limits_of_shape J D] (F : J ⥤ C ⥤ D) (X : C) :
  (limit F).obj X ≅ limit (F.flip.obj X) :=
limits.limit_obj_iso_limit_comp_evaluation F X

end category_theory.limits
