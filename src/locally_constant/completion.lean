import topology.continuous_function.compact

import for_mathlib.SemiNormedGroup

import locally_constant.completion_aux
import free_pfpng.main
import prop819
.

noncomputable theory

universes u

open category_theory opposite ProFiltPseuNormGrp₁
open function (surjective)
open_locale nnreal

variables (S : Profinite.{u})
variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]
variables (V' : Type u) [normed_add_comm_group V'] [complete_space V']

def LCC : Profinite.{u}ᵒᵖ ⥤ Ab.{u} :=
SemiNormedGroup.LCC.obj V ⋙ forget₂ _ _

local attribute [instance] locally_constant.seminormed_add_comm_group locally_constant.pseudo_metric_space

open uniform_space

lemma continuous_map.bdd_above_range_norm (f : C(S, V')) :
  bdd_above (set.range (λ (s : ↥S), ∥f s∥)) :=
(is_compact_range $ continuous_norm.comp f.continuous).bdd_above

def Condensed.of_top_ab_map_normed_group_hom {S T : Profinite.{u}ᵒᵖ} (f : S ⟶ T) :
  normed_add_group_hom C(_, V') C(_, V') :=
{ to_fun := (Condensed.of_top_ab.presheaf.{u} V').map f,
  map_add' := λ _ _, add_monoid_hom.map_add _ _ _,
  bound' := begin
    refine ⟨1, λ g, _⟩,
    rw [one_mul, continuous_map.norm_eq_supr_norm],
    casesI is_empty_or_nonempty.{u+1} (unop T : Profinite),
    { simp only [real.csupr_empty], apply norm_nonneg },
    apply csupr_le,
    intro s,
    rw [continuous_map.norm_eq_supr_norm],
    exact le_csupr (continuous_map.bdd_above_range_norm _ _ _) (f.unop s),
  end }

lemma Condensed.of_top_ab_map_continuous {S T : Profinite.{u}ᵒᵖ} (f : S ⟶ T) :
  @continuous C(_, V') C(_, V') _ _
    ((Condensed.of_top_ab.presheaf.{u} V').map f) :=
(Condensed.of_top_ab_map_normed_group_hom V' f).continuous

lemma locally_constant.to_continuous_map_isometry :
  isometry (locally_constant.to_continuous_map : locally_constant S V' → C(S, V')) :=
begin
  intros f g,
  simp only [edist_dist, dist_eq_norm, continuous_map.norm_eq_supr_norm,
    locally_constant.norm_def, locally_constant.to_continuous_map_eq_coe,
    continuous_map.coe_sub, locally_constant.coe_continuous_map, pi.sub_apply],
  refl,
end

lemma locally_constant.to_continuous_map_uniform_inducing :
  uniform_inducing (locally_constant.to_continuous_map : locally_constant S V' → C(S, V')) :=
(locally_constant.to_continuous_map_isometry S V').uniform_inducing

lemma locally_constant.to_continuous_map_uniform_continuous :
  uniform_continuous (locally_constant.to_continuous_map : locally_constant S V' → C(S, V')) :=
(locally_constant.to_continuous_map_uniform_inducing S V').uniform_continuous

lemma locally_constant.to_continuous_map_dense_range :
  dense_range (locally_constant.to_continuous_map : locally_constant S V' → C(S, V')) :=
locally_constant.density.loc_const_dense _

def locally_constant.pkg : abstract_completion (locally_constant S V') :=
{ space := C(S, V'),
  coe := locally_constant.to_continuous_map,
  uniform_struct := by apply_instance,
  complete := by apply_instance,
  separation := by apply_instance,
  uniform_inducing := locally_constant.to_continuous_map_uniform_inducing S V',
  dense := locally_constant.to_continuous_map_dense_range S V', }

def LCC_iso_Cond_of_top_ab_equiv :
  completion (locally_constant S V') ≃ C(S, V') :=
(@completion.cpkg (locally_constant S V') _).compare_equiv (locally_constant.pkg S V')

def LCC_iso_Cond_of_top_ab_add_equiv :
  completion (locally_constant S V') ≃+ C(S, V') :=
{ to_fun := completion.extension locally_constant.to_continuous_map,
  map_add' := begin
    intros f g,
    apply completion.induction_on₂ f g,
    { apply is_closed_eq,
      { exact completion.continuous_extension.comp continuous_add },
      { exact (completion.continuous_extension.comp continuous_fst).add
              (completion.continuous_extension.comp continuous_snd), } },
    { clear f g, intros f g,
      rw [← completion.coe_add,
        completion.extension_coe, completion.extension_coe, completion.extension_coe],
      { refl },
      all_goals { apply locally_constant.to_continuous_map_uniform_continuous } }
  end,
  .. LCC_iso_Cond_of_top_ab_equiv S V' }

lemma LCC_iso_Cond_of_top_ab_natural {S T : Profinite.{u}} (f : S ⟶ T) :
  LCC_iso_Cond_of_top_ab_add_equiv S V' ∘
  completion.map (locally_constant.comap f) =
  (Condensed.of_top_ab.presheaf.{u} V').map f.op ∘
  LCC_iso_Cond_of_top_ab_add_equiv T V' :=
begin
  dsimp [LCC_iso_Cond_of_top_ab_add_equiv],
  apply completion.ext,
  { refine completion.continuous_extension.comp completion.continuous_map, },
  { refine (Condensed.of_top_ab_map_continuous _ _).comp completion.continuous_extension, },
  intro g,
  ext s,
  simp only [function.comp_app],
  rw [completion.map_coe, completion.extension_coe, completion.extension_coe,
    locally_constant.to_continuous_map_eq_coe, locally_constant.coe_continuous_map,
    locally_constant.to_continuous_map_eq_coe, locally_constant.coe_comap],
  { refl },
  { exact f.continuous },
  { apply locally_constant.to_continuous_map_uniform_continuous },
  { apply locally_constant.to_continuous_map_uniform_continuous },
  { exact (locally_constant.comap_hom f f.2).uniform_continuous, }
end

def LCC_iso_Cond_of_top_ab :
  LCC.{u} V ≅ Condensed.of_top_ab.presheaf.{u} V :=
nat_iso.of_components
  (λ S, add_equiv.to_AddCommGroup_iso $ LCC_iso_Cond_of_top_ab_add_equiv (unop S) V)
  begin
    intros S T f,
    ext1 φ,
    have := LCC_iso_Cond_of_top_ab_natural V f.unop,
    convert congr_fun this φ using 1,
    clear this,
    delta LCC SemiNormedGroup.LCC,
    simp only [add_equiv.to_AddCommGroup_iso_hom, category_theory.comp_apply,
      add_equiv.coe_to_add_monoid_hom, add_equiv.apply_eq_iff_eq,
      functor.comp_map, curry_obj_obj_map, uncurry_obj_map,
      category_theory.functor.map_id, nat_trans.id_app,
      SemiNormedGroup.LocallyConstant_obj_map,
      SemiNormedGroup.Completion_map],
    erw [category.id_comp],
    refl,
  end

def Condensed_LCC : Condensed.{u} Ab.{u+1} :=
{ val := LCC.{u} V ⋙ Ab.ulift.{u+1},
  cond := begin
    let e := LCC_iso_Cond_of_top_ab V,
    let e' := iso_whisker_right e Ab.ulift.{u+1},
    apply presheaf.is_sheaf_of_iso proetale_topology.{u} e',
    exact (Condensed.of_top_ab _).2,
  end }

def Condensed_LCC_iso_of_top_ab :
  Condensed_LCC V ≅ Condensed.of_top_ab V :=
Sheaf.iso.mk _ _ $ iso_whisker_right (LCC_iso_Cond_of_top_ab _) _
