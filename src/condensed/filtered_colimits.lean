import condensed.is_proetale_sheaf
import condensed.adjunctions
import category_theory.limits.filtered_colimit_commutes_finite_limit

open category_theory
open category_theory.limits

universe u
variables
  {J : Type (u+1)} [small_category J] [is_filtered J]
  {C : Type (u+2)}
  [category.{u+1} C]
  [concrete_category.{u+1} C]
  [has_limits C]
  [has_colimits_of_shape J C]
  [preserves_colimits_of_shape J (forget C)]
  [preserves_limits (forget C)]
  (F : J ⥤ Condensed.{u} C)

lemma is_sheaf_colimit_presheaf :
  presheaf.is_sheaf proetale_topology (colimit (F ⋙ Sheaf_to_presheaf _ _)) :=
begin
  --rw is_sheaf_iff_is_sheaf_of_type,
  let G := (colimit (F ⋙ Sheaf_to_presheaf _ _)),
  let Gs := F ⋙ Sheaf_to_presheaf _ _,
  have hGs : ∀ j, presheaf.is_sheaf proetale_topology (Gs.obj j),
  { intros j, exact (F.obj j).2 },
  have hGsempty : ∀ j, (Gs.obj j).empty_condition',
  { intros j, specialize hGs j,
    rw (Gs.obj j).is_proetale_sheaf_tfae.out 0 3 at hGs,
    exact hGs.1 },
  have hGsproj : ∀ j, (Gs.obj j).product_condition',
  { intros j, specialize hGs j,
    rw (Gs.obj j).is_proetale_sheaf_tfae.out 0 3 at hGs,
    exact hGs.2.1 },
  have hGseq : ∀ j, (Gs.obj j).equalizer_condition',
  { intros j, specialize hGs j,
    rw (Gs.obj j).is_proetale_sheaf_tfae.out 0 3 at hGs,
    exact hGs.2.2 },
  rw G.is_proetale_sheaf_tfae.out 0 3,
  refine ⟨_,_,_⟩,
  { sorry },
  { sorry },
  { sorry },
end
