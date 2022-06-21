import for_mathlib.exact_functor
import for_mathlib.ab4
import for_mathlib.abelian_sheaves.functor_category
import for_mathlib.homological_complex2
import category_theory.limits.preserves.filtered

namespace category_theory

open category_theory.limits

universes v u
variables (A : Type u) [category.{v} A] [abelian A] [has_colimits A]

instance colim_additive (J : Type v) [small_category J]:
  functor.additive (limits.colim : ((J ⥤ A) ⥤ A)) := ⟨⟩ .

class AB5 : Prop :=
(cond [] : ∀ (J : Type v) [small_category J] [is_filtered J],
  functor.exact (limits.colim : (J ⥤ A) ⥤ A))

lemma AB5.colim_exact [AB5 A] (J : Type v) [small_category J] [is_filtered J] :
  functor.exact (limits.colim : (J ⥤ A) ⥤ A) :=
AB5.cond A J

instance homology_functor_preserves_filtered_colimit
  {M : Type} (c : complex_shape M) (i : M)
  (J : Type v) [small_category J] [is_filtered J]
  (F : J ⥤ homological_complex A c) :
  preserves_colimit F (homology_functor A c i) :=
begin
  sorry
end

instance homology_functor_preserves_filtered_colimits
  {M : Type} (c : complex_shape M) (i : M) :
  preserves_filtered_colimits
  (homology_functor A c i : homological_complex A c ⥤ A) :=
begin
  constructor, introsI J _ _, constructor
end

end category_theory
