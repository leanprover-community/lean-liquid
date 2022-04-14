import topology.continuous_function.compact

import free_pfpng.main
import condensed.acyclic
import prop819
.

noncomputable theory

universes u

open category_theory opposite ProFiltPseuNormGrp₁
open function (surjective)
open_locale nnreal

variables (S : Profinite.{u})
variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]
variables (V' : Type u) [normed_group V'] [complete_space V']

set_option pp.universes true

-- move me
instance SemiNormedGroup.forget₂ : has_forget₂ SemiNormedGroup.{u} Ab.{u} :=
{ forget₂ :=
  { obj := λ V, AddCommGroup.of V,
    map := λ V W f, f.to_add_monoid_hom,
    map_id' := λ V, rfl,
    map_comp' := λ _ _ _ f g, rfl },
  forget_comp := rfl }

-- move me
instance SemiNormedGroup.forget₂_additive :
  (forget₂ SemiNormedGroup.{u} Ab.{u}).additive :=
{ map_add' := by { intros, refl } }

def LCC : Profinite.{u}ᵒᵖ ⥤ Ab.{u} :=
SemiNormedGroup.LCC.obj V ⋙ forget₂ _ _

local attribute [instance] locally_constant.semi_normed_group locally_constant.pseudo_metric_space

open uniform_space

lemma continuous_map.bdd_above_range_norm (f : C(S, V')) :
  bdd_above (set.range (λ (s : ↥S), ∥f s∥)) :=
(is_compact_range $ continuous_norm.comp f.continuous).bdd_above

def Condensed.of_top_ab_map_normed_group_hom {S T : Profinite.{u}ᵒᵖ} (f : S ⟶ T) :
  normed_group_hom C(_, V') C(_, V') :=
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

@[simps]
def locally_constant.to_continuous_map_hom :
  normed_group_hom (locally_constant S V') C(S, V') :=
{ to_fun := locally_constant.to_continuous_map,
  map_add' := λ f g, rfl,
  bound' := by { refine ⟨1, λ f, _⟩, rw one_mul, rw [continuous_map.norm_eq_supr_norm], refl, } }

lemma locally_constant.to_continuous_map_uniform_continuous :
  uniform_continuous (locally_constant.to_continuous_map : locally_constant S V' → C(S, V')) :=
(locally_constant.to_continuous_map_hom S V').uniform_continuous

def LCC_iso_Cond_of_top_ab_hom :
  completion (locally_constant S V') →+ C(S, V') :=
add_monoid_hom.mk' (completion.extension $ locally_constant.to_continuous_map) $
begin
  intros f g,
  apply completion.induction_on₂ f g,
  { apply is_closed_eq,
    { exact completion.continuous_extension.comp continuous_add },
    { -- exact completion.continuous_extension.add completion.continuous_extension,
      sorry } },
  { sorry }
end

def LCC_iso_Cond_of_top_ab_equiv :
  completion (locally_constant S V') ≃+ C(S, V') :=
add_equiv.of_bijective (LCC_iso_Cond_of_top_ab_hom S V')
begin
  split,
  { rw add_monoid_hom.injective_iff,
    intros f,
    apply completion.induction_on f; clear f,
    { sorry },
    intros f hf,
    have := @locally_constant.to_continuous_map_injective S V' _ _ f 0,
    sorry },
  { sorry }
end

lemma LCC_iso_Cond_of_top_ab_natural {S T : Profinite.{u}} (f : S ⟶ T) :
  LCC_iso_Cond_of_top_ab_equiv S V' ∘
  completion.map (locally_constant.comap f) =
  (Condensed.of_top_ab.presheaf.{u} V').map f.op ∘
  LCC_iso_Cond_of_top_ab_equiv T V' :=
begin
  dsimp [LCC_iso_Cond_of_top_ab_equiv, LCC_iso_Cond_of_top_ab_hom, add_equiv.of_bijective,
    equiv.of_bijective],
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

instance SemiNormedGroup.metric_space : metric_space V :=
metric.of_t2_pseudo_metric_space ‹_›

instance SemiNormedGroup.normed_group : normed_group V :=
{ dist_eq := semi_normed_group.dist_eq,
  ..(by apply_instance : semi_normed_group V) }

def LCC_iso_Cond_of_top_ab :
  LCC.{u} V ≅ Condensed.of_top_ab.presheaf.{u} V :=
nat_iso.of_components
  (λ S, add_equiv.to_AddCommGroup_iso $ LCC_iso_Cond_of_top_ab_equiv (unop S) V)
  begin
    intros S T f,
    ext1 φ,
    have := LCC_iso_Cond_of_top_ab_natural V f.unop,
    convert congr_fun this φ using 1,
    clear this,
    delta LCC SemiNormedGroup.LCC,
    simp only [add_equiv.to_AddCommGroup_iso_hom, category_theory.comp_apply,
      add_equiv.coe_to_add_monoid_hom, add_equiv.apply_eq_iff_eq,
      functor.comp_map, curry.obj_obj_map, uncurry.obj_map,
      category_theory.functor.map_id, nat_trans.id_app,
      SemiNormedGroup.LocallyConstant_obj_map,
      SemiNormedGroup.Completion_map],
    erw [category.id_comp],
    refl,
  end
