import algebra.category.Group.abelian
import algebra.category.Group.filtered_colimits

open category_theory

namespace AddCommGroup

universes u

variables {J : Type u} [small_category J] [is_filtered J]

set_option pp.universes true

noncomputable theory

-- Axiom AB5 for `AddCommGroup`
theorem exact_colim_map_iff_of_is_filtered
  (F G H : J ⥤ AddCommGroup.{u}) (η : F ⟶ G) (γ : G ⟶ H) :
  exact (limits.colim_map η) (limits.colim_map γ) ↔ (∀ j, exact (η.app j) (γ.app j)) :=
sorry

end AddCommGroup
