import for_mathlib.ab5

namespace category_theory

universes v u
variables {A : Type u} [category.{v} A] [abelian A]
  [limits.has_colimits A] [AB5 A]

def mono_colim_map_of_mono {J : Type v}
  [small_category J] [is_filtered J] {F G : J ⥤ A}
  (η : F ⟶ G) [∀ i, mono (η.app i)] :
  mono (limits.colim_map η) := sorry

end category_theory
