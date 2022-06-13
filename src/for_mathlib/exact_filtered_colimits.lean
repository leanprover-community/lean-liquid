import algebra.category.Group.abelian
import algebra.category.Group.filtered_colimits
import category_theory.limits.concrete_category
import for_mathlib.AddCommGroup.exact
import for_mathlib.ab5

.

open category_theory

namespace AddCommGroup

universes u

variables {J : Type u} [small_category J] [is_filtered J]

noncomputable theory

-- Axiom AB5 for `AddCommGroup`
theorem exact_colim_of_exact_of_is_filtered
  (F G H : J ⥤ AddCommGroup.{u}) (η : F ⟶ G) (γ : G ⟶ H) :
  (∀ j, exact (η.app j) (γ.app j)) → exact (limits.colim_map η) (limits.colim_map γ) :=
begin
  intros h,
  rw AddCommGroup.exact_iff', split,
  { ext1 j, simp [reassoc_of (h j).1] },
  { rintros x (hx : _ = _),
    obtain ⟨j,y,rfl⟩ := limits.concrete.colimit_exists_rep _ x,
    erw [← comp_apply, limits.colimit.ι_desc] at hx, dsimp at hx,
    rw comp_apply at hx,
    have : (0 : limits.colimit H) = limits.colimit.ι H j 0, by simp, rw this at hx, clear this,
    obtain ⟨k,e₁,e₂,hk⟩ := limits.concrete.colimit_exists_of_rep_eq _ _ _ hx,
    simp only [map_zero, ← comp_apply, ← nat_trans.naturality] at hk, rw comp_apply at hk,
    obtain ⟨t,ht⟩ := ((AddCommGroup.exact_iff' _ _).1 (h k)).2 hk,
    use limits.colimit.ι F k t,
    erw [← comp_apply, limits.colimit.ι_map, comp_apply, ht, ← comp_apply],
    congr' 1, simp }
end

instance AB5 : AB5 AddCommGroup.{u} :=
begin
  constructor, introsI J _ _, intros F G H f g h,
  apply exact_colim_of_exact_of_is_filtered,
  exact (nat_trans.exact_iff_forall.{(u+1) u u} f g).1 h,
end

end AddCommGroup
