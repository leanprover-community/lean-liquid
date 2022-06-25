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

/-
TODO: Change `AB5` from this definition to saying that `colim : (J ⥤ A) ⥤ A`
preserves finite limits and colimits whenever `J` is filtered.
-/
class AB5 : Prop :=
(cond [] : ∀ (J : Type v) [small_category J] [is_filtered J],
  functor.exact (limits.colim : (J ⥤ A) ⥤ A))

variables (J : Type v) [small_category J] [is_filtered J]

lemma AB5.colim_exact [AB5 A] :
  functor.exact (limits.colim : (J ⥤ A) ⥤ A) :=
AB5.cond A J

variables
  [preserves_finite_limits (limits.colim : (J ⥤ A) ⥤ A)]
  [preserves_finite_colimits (limits.colim : (J ⥤ A) ⥤ A)]

noncomputable
def colimit_homology_functor_iso
  {M : Type} (c : complex_shape M) (i : M) :
  homology_functor (J ⥤ A) c i ⋙ limits.colim ≅
  (limits.colim.map_homological_complex _) ⋙ homology_functor _ _ i :=
functor.homology_functor_iso _ _ _

noncomputable
def eval_functor_colimit_iso
  {M : Type} (c : complex_shape M)
  (F : J ⥤ homological_complex A c) :
  colimit F ≅ (limits.colim.map_homological_complex c).obj
  (homological_complex.eval_functor.obj F) :=
homological_complex.hom.iso_of_components
(λ i, preserves_colimit_iso (homological_complex.eval A c i) _)
begin
  intros i j hij,
  rw ←iso.eq_inv_comp,
  apply colimit.hom_ext,
  intro k,
  dsimp,
  simp only [colimit.ι_map, whisker_left_app, ι_preserves_colimits_iso_inv_assoc,
    homological_complex.eval_map, homological_complex.hom.comm_assoc],
  congr,
  rw [preserves_colimit_iso, ← limits.colimit.iso_colimit_cocone_ι_inv
    ⟨_, preserves_colimit.preserves (colimit.is_colimit F)⟩],
  refl
end

local attribute [reassoc] nat_trans.comp_app

noncomputable! -- UUUUGGGGHHH
instance homology_functor_preserves_filtered_colimit
  {M : Type} (c : complex_shape M) (i : M)
  (F : J ⥤ homological_complex A c) :
  preserves_colimit F (homology_functor A c i) :=
begin
  let F' := homological_complex.eval_functor_equiv.functor.obj F,
  let q := (colimit_homology_functor_iso A J c i).app F',
  dsimp at q,
  apply preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit F),
  let e : F ⋙ homology_functor A c i ≅ F'.homology i :=
    homological_complex.eval_functor_homology_iso _ _,
  apply (limits.is_colimit.precompose_inv_equiv e
    ((homology_functor A c i).map_cocone (colimit.cocone F))).to_fun,
  suffices y : colimit.cocone _ ≅
    (cocones.precompose e.inv).obj
    ((homology_functor A c i).map_cocone (colimit.cocone F)),
  { apply limits.is_colimit.of_iso_colimit (colimit.is_colimit _) y },
  refine cocones.ext (q ≪≫ _) _,
  { apply (homology_functor A c i).map_iso,
    exact (eval_functor_colimit_iso _ _ _ _).symm },
  { intro j,
    dsimp,

    -- Not sure if the following is a sensible approach...
    rw [←iso.app_inv, iso.eq_inv_comp],
    ext,
    simp only [homology.map_ι, category.assoc],
    rw [homology.π'_ι_assoc, cokernel.π_desc],
    dsimp,
    dsimp [colimit_homology_functor_iso, colim.homology_functor_iso],
    erw [homology.lift_ι_assoc],
    slice_lhs 3 4 { rw colimit.ι_map, },
    simp only [category.assoc],
    simp only [←preserves_cokernel.iso_inv],
    rw [is_iso.iso.inv_inv],

    sorry }
end

noncomputable
instance homology_functor_preserves_filtered_colimits
  {M : Type} (c : complex_shape M) (i : M)
  [∀ (J : Type v) [hJ : small_category J]
    [@is_filtered J hJ],
    by exactI preserves_finite_limits (limits.colim : (J ⥤ A) ⥤ A)]
  [∀ (J : Type v) [hJ : small_category J]
    [@is_filtered J hJ],
    by exactI preserves_finite_colimits (limits.colim : (J ⥤ A) ⥤ A)] :
  preserves_filtered_colimits
  (homology_functor A c i : homological_complex A c ⥤ A) :=
begin
  constructor, introsI J _ _, constructor,
end

end category_theory
