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

instance : has_norm C(S, V) :=
⟨λ f, ⨆ s, ∥f s∥⟩

lemma continuous_map.norm_def (f : C(S, V)) : ∥f∥ = ⨆ s, ∥f s∥ := rfl

lemma continuous_map.bdd_above_range_norm (f : C(S, V)) :
  bdd_above (set.range (λ (s : ↥S), ∥f s∥)) :=
(is_compact_range $ continuous_norm.comp f.continuous).bdd_above

instance : semi_normed_group C(S, V) :=
semi_normed_group.of_core _ $
{ norm_zero := by { simp only [continuous_map.norm_def, continuous_map.coe_zero,
    pi.zero_apply, norm_zero, real.csupr_const_zero], },
  triangle := λ f g, begin
    simp only [continuous_map.norm_def],
    casesI is_empty_or_nonempty S,
    { simp only [real.csupr_empty, zero_add], },
    apply csupr_le,
    intro s,
    calc ∥(f + g) s∥ ≤ ∥f s∥ + ∥g s∥ : norm_add_le _ _
    ... ≤ ∥f∥ + ∥g∥ : add_le_add (le_csupr _ s) (le_csupr _ s),
    { apply continuous_map.bdd_above_range_norm },
    { apply continuous_map.bdd_above_range_norm },
  end,
  norm_neg := λ f, by { simp only [continuous_map.norm_def, continuous_map.coe_neg,
    pi.neg_apply, norm_neg], }, }

instance : complete_space C(S, V) := sorry
instance : separated_space C(S, V) := sorry
instance : uniform_add_group C(S, V) := sorry

lemma Condensed.of_top_ab_map_continuous {S T : Profinite.{u}ᵒᵖ} (f : S ⟶ T) :
  @continuous C(_, V) C(_, V) _ _
    ((Condensed.of_top_ab.presheaf.{u} V).map f) :=
sorry

def locally_constant.to_continuous_map_hom :
  locally_constant S V →+ C(S, V) :=
add_monoid_hom.mk' locally_constant.to_continuous_map $ λ f g, rfl

lemma locally_constant.to_continuous_map_uniform_continuous :
  uniform_continuous (locally_constant.to_continuous_map : locally_constant S V → C(S, V)) :=
begin
  refine (locally_constant.to_continuous_map_hom S V).uniform_continuous_of_continuous_at_zero _,
  sorry
end

def LCC_iso_Cond_of_top_ab_fun :
  completion (locally_constant S V) → C(S, V) :=
completion.extension $ locally_constant.to_continuous_map

def LCC_iso_Cond_of_top_ab_equiv :
  completion (locally_constant S V) ≃ C(S, V) :=
equiv.of_bijective (LCC_iso_Cond_of_top_ab_fun S V)
begin
  split,
  { have := @locally_constant.to_continuous_map_injective S V _ _,
    sorry },
  { sorry }
end

def LCC_iso_Cond_of_top_ab_obj :
  completion (locally_constant S V) ≃+ C(S, V) :=
{ map_add' := λ f g, begin
    sorry
  end,
  .. LCC_iso_Cond_of_top_ab_equiv S V }

lemma LCC_iso_Cond_of_top_ab_natural {S T : Profinite.{u}} (f : S ⟶ T) :
  LCC_iso_Cond_of_top_ab_obj S V ∘
  completion.map (locally_constant.comap f) =
  (Condensed.of_top_ab.presheaf.{u} V).map f.op ∘
  LCC_iso_Cond_of_top_ab_obj T V :=
begin
  dsimp [LCC_iso_Cond_of_top_ab_obj, LCC_iso_Cond_of_top_ab_equiv, LCC_iso_Cond_of_top_ab_fun,
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

def LCC_iso_Cond_of_top_ab :
  LCC.{u} V ≅ Condensed.of_top_ab.presheaf.{u} V :=
nat_iso.of_components
  (λ S, add_equiv.to_AddCommGroup_iso $ LCC_iso_Cond_of_top_ab_obj _ _)
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
