import pseudo_normed_group.category.strictProFiltPseuNormGrpWithTinv
import laurent_measures.functor
import condensed.ab
import condensed.rescale
import condensed.exact
import for_mathlib.split_exact
.

noncomputable theory

universe u

open_locale nnreal
open category_theory

variables {C D : Type*} [category C] [category D] (r' : ℝ≥0) [fact (0 < r')]

abbreviation category_theory.nat_trans.conj_by {F G : C ⥤ D} (α : F ≅ G) (β : G ⟶ G) :
  F ⟶ F := α.hom ≫ β ≫ α.inv

open category_theory

abbreviation ProFiltPseuNormGrpWithTinv₁.to_CHFPNG₁ :
  ProFiltPseuNormGrpWithTinv₁.{u} r' ⥤ CompHausFiltPseuNormGrp₁.{u} :=
ProFiltPseuNormGrpWithTinv₁.to_PFPNG₁ r' ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁

open ProFiltPseuNormGrpWithTinv₁ CompHausFiltPseuNormGrp₁ CompHausFiltPseuNormGrp

variables {r'}

def condensify (F : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
Profinite.extend.{u} F ⋙ enlarging_functor.{u} ⋙ to_Condensed.{u}

variables {F G H : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}}

def condensify_map (α : F ⟶ G) : condensify F ⟶ condensify G :=
whisker_right (Profinite.extend_nat_trans α) _

lemma condensify_map_id (F : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  condensify_map (𝟙 F) = 𝟙 (condensify F) :=
by simpa only [condensify_map, Profinite.extend_nat_trans_id] using whisker_right_id _

lemma condensify_map_comp (α : F ⟶ G) (β : G ⟶ H) :
  condensify_map (α ≫ β) = condensify_map α ≫ condensify_map β :=
by simp only [condensify_map, Profinite.extend_nat_trans_comp, whisker_right_comp]

def condensify_def (F : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  condensify F ≅ Profinite.extend.{u} F ⋙ enlarging_functor.{u} ⋙ to_Condensed.{u} :=
iso.refl _

def Tinv_nat_trans (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  (F ⋙ to_CHFPNG₁.{u} r') ⋙ enlarging_functor ⟶
  (F ⋙ to_CHFPNG₁.{u} r') ⋙ enlarging_functor :=
{ app := λ X, profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv,
  naturality' := λ X Y f, by { ext x, exact ((F.map f).map_Tinv x).symm } }

def Tinv2_nat_trans (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  (F ⋙ to_CHFPNG₁.{u} r') ⋙ enlarging_functor ⟶
  (F ⋙ to_CHFPNG₁.{u} r') ⋙ enlarging_functor :=
Tinv_nat_trans F - 2 • 𝟙 _

lemma Tinv_bound_by (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') (X : C) :
  ((Tinv_nat_trans F).app X).bound_by r'⁻¹ :=
profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv_bound_by

lemma twoid_bound_by (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') (X : C) :
  comphaus_filtered_pseudo_normed_group_hom.bound_by
    ((2 • 𝟙 ((F ⋙ to_CHFPNG₁ r') ⋙ enlarging_functor)).app X) 2 :=
begin
  simp only [nat_trans.app_nsmul, nat_trans.id_app],
  refine ((comphaus_filtered_pseudo_normed_group_hom.mk_of_bound_bound_by _ 1 _).nsmul 2).mono _ _,
  norm_num,
end

lemma Tinv2_bound_by (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') (X : C) :
  ((Tinv2_nat_trans F).app X).bound_by (r'⁻¹ + 2) :=
(Tinv_bound_by F X).sub (twoid_bound_by F X)

@[reassoc]
lemma Tinv_nat_trans_comp {F G : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r'} (α : F ⟶ G) :
  Tinv_nat_trans F ≫ @whisker_right _ _ _ _ _ _ F G α (to_CHFPNG₁ r' ⋙ enlarging_functor.{u}) =
  @whisker_right _ _ _ _ _ _ F G α (to_CHFPNG₁ r' ⋙ enlarging_functor.{u}) ≫ Tinv_nat_trans G :=
by { ext X x, exact (α.app X).map_Tinv x }

def condensify_Tinv (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  condensify.{u} (F ⋙ to_CHFPNG₁ r') ⟶ condensify.{u} (F ⋙ to_CHFPNG₁ r') :=
@whisker_right _ _ _ _ _ _ _ _
  (nat_trans.conj_by
    (iso_whisker_right (Profinite.extend_commutes _ _).symm enlarging_functor.{u}) $
      Tinv_nat_trans.{u} (Profinite.extend.{u} F)) _

lemma condensify_map_comp_Tinv {F G : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r'}
  (α : F ⟶ G) :
  condensify_map (whisker_right α (to_CHFPNG₁ r')) ≫ condensify_Tinv G =
  condensify_Tinv F ≫ condensify_map (whisker_right α (to_CHFPNG₁ r')) :=
begin
  delta condensify_map condensify_Tinv nat_trans.conj_by,
  simp only [Profinite.extend_nat_trans_whisker_right],
  simp only [iso.symm_hom, iso_whisker_right_hom, iso_whisker_right_inv, iso.symm_inv,
    whisker_right_comp, category.assoc],
  simp only [← nat_trans.comp_app, ← whisker_right_twice enlarging_functor, category.comp_id,
    ← whisker_right_comp, ← whisker_right_comp_assoc, iso.hom_inv_id, iso.hom_inv_id_assoc],
  congr' 1,
  simp only [whisker_right_comp, category.assoc, whisker_right_twice],
  rw Tinv_nat_trans_comp_assoc,
end
.

set_option pp.universes true

def condensify_nonstrict
  (α : F ⋙ enlarging_functor.{u} ⟶ G ⋙ enlarging_functor.{u}) (c : ℝ≥0) [fact (0 < c)]
  (h : ∀ X, (α.app X).bound_by c) :
  condensify F ⟶ condensify G :=
(functor.associator _ _ _).inv ≫
  whisker_right (nonstrict_extend.{u} α c h) to_Condensed ≫
  (functor.associator _ _ _).hom

section

variables (α β : F ⋙ enlarging_functor.{u} ⟶ G ⋙ enlarging_functor.{u})
variables (c cα cβ cαβ : ℝ≥0) [fact (0 < c)]  [fact (0 < cα)] [fact (0 < cβ)] [fact (0 < cαβ)]

lemma condensify_nonstrict_map_add
  (hα : ∀ X, (α.app X).bound_by cα) (hβ : ∀ X, (β.app X).bound_by cβ)
  (hαβ : ∀ X, ((α + β).app X).bound_by cαβ) :
  condensify_nonstrict (α + β) cαβ hαβ =
  condensify_nonstrict α cα hα + condensify_nonstrict β cβ hβ :=
begin
  delta condensify_nonstrict,
  rw [nonstrict_extend_map_add _ _ cα cβ cαβ hα hβ],
  refl,
end

lemma condensify_nonstrict_map_neg
  (hα : ∀ X, (α.app X).bound_by cα) (hβ : ∀ X, ((-α).app X).bound_by cβ) :
  condensify_nonstrict (-α) cβ hβ = -condensify_nonstrict α cα hα :=
begin
  delta condensify_nonstrict,
  rw [nonstrict_extend_map_neg _ _ cβ hα],
  refl,
end

lemma condensify_nonstrict_map_sub
  (hα : ∀ X, (α.app X).bound_by cα) (hβ : ∀ X, (β.app X).bound_by cβ)
  (hαβ : ∀ X, ((α - β).app X).bound_by cαβ) :
  condensify_nonstrict (α - β) cαβ hαβ =
  condensify_nonstrict α cα hα - condensify_nonstrict β cβ hβ :=
begin
  delta condensify_nonstrict,
  rw [nonstrict_extend_map_sub _ _ cα cβ cαβ hα hβ],
  refl,
end

lemma condensify_nonstrict_map_nsmul (n : ℕ)
  (hα : ∀ X, (α.app X).bound_by cα) (hβ : ∀ X, ((n • α).app X).bound_by cβ) :
  condensify_nonstrict (n • α) cβ hβ = n • condensify_nonstrict α cα hα :=
begin
  delta condensify_nonstrict,
  rw [nonstrict_extend_map_nsmul _ _ cβ n hα],
  clear hβ,
  induction n with n ih,
  { rw [zero_smul, zero_smul], refl },
  { rw [succ_nsmul, succ_nsmul, ← ih], refl, }
end

-- move me
instance fact_inv_pos : fact (0 < r'⁻¹) := sorry

lemma condensify_nonstrict_Tinv (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  condensify_nonstrict (Tinv_nat_trans F) r'⁻¹ (Tinv_bound_by _) = condensify_Tinv F :=
begin
  sorry
end

end

open pseudo_normed_group (filtration)

lemma condensify_exact (α : F ⟶ G) (β : G ⟶ H) (cα : ℝ≥0) (hcα : 1 ≤ cα) (cβ : ℝ≥0) (hcβ : 1 ≤ cβ)
  (H1 : ∀ S, function.injective (α.app S))
  (H2a : ∀ S, (α.app S) ≫ (β.app S) = 0)
  (H2b : ∀ S c, (β.app S) ⁻¹' {0} ∩ filtration (G.obj S) c ⊆
    (α.app S) '' filtration (F.obj S) (cα * c))
  (H3a : ∀ S, function.surjective (β.app S))
  (H3b : ∀ S c, filtration (H.obj S) c ⊆ (β.app S) '' filtration (G.obj S) (cβ * c))
  (X : Profinite.{u}) :
  short_exact ((condensify_map α).app X) ((condensify_map β).app X) :=
begin
  apply_with short_exact.mk { instances := ff },
  { apply condensed.mono_to_Condensed_map,
    apply exact_with_constant_extend_zero_left,
    intro S,
    apply_with exact_with_constant_of_mono { instances := ff },
    rw AddCommGroup.mono_iff_injective,
    exact H1 S, },
  { apply condensed.epi_to_Condensed_map _ cβ hcβ,
    apply exact_with_constant_extend_zero_right,
    intro S,
    apply_with exact_with_constant_of_epi { instances := ff },
    swap, { exact H3b S },
    rw AddCommGroup.epi_iff_surjective,
    exact H3a S },
  { apply condensed.exact_of_exact_with_constant _ _ cα hcα,
    apply exact_with_constant_extend,
    intro S,
    refine ⟨H2a S, H2b S⟩, }
end

lemma exact_of_iso_comp_exact {V : Type u} [category V] [limits.has_images V]
  [limits.has_zero_morphisms V] [limits.has_equalizers V]
  {A B C D : V} (f : A ⟶ B) {g : B ⟶ C} {h : C ⟶ D} (hf : is_iso f) (hgh : exact g h) :
  exact (f ≫ g) h :=
by rwa exact_iso_comp

lemma condensify_nonstrict_exact
  (α : F ⋙ enlarging_functor.{u} ⟶ G ⋙ enlarging_functor.{u}) (β : G ⟶ H)
  (c : ℝ≥0) [fact (0 < c)]
  (h : ∀ X, (α.app X).bound_by c)
  (cα : ℝ≥0) (hcα : 1 ≤ cα) (cβ : ℝ≥0) (hcβ : 1 ≤ cβ)
  (H1 : ∀ S, function.injective (α.app S))
  (H2a : ∀ S, (α.app S) ≫ ((whisker_right β _).app S) = 0)
  (H2b : ∀ S c', (β.app S) ⁻¹' {0} ∩ filtration (G.obj S) c' ⊆
    (α.app S) '' filtration (F.obj S) (cα * c' * c⁻¹))
  (H3a : ∀ S, function.surjective (β.app S))
  (H3b : ∀ S c', filtration (H.obj S) c' ⊆ (β.app S) '' filtration (G.obj S) (cβ * c'))
  (X : Profinite.{u}) :
  short_exact ((condensify_nonstrict α c h).app X) ((condensify_map β).app X) :=
begin
  apply_with short_exact.mk { instances := ff },
  { simp only [condensify_nonstrict, nonstrict_extend, whisker_right_comp],
    repeat { apply_with mono_comp { instances := ff }; try { apply_instance } },
    apply condensed.mono_to_Condensed_map,
    apply exact_with_constant_extend_zero_left,
    intro S,
    apply_with exact_with_constant_of_mono { instances := ff },
    rw AddCommGroup.mono_iff_injective,
    exact H1 S, },
  { apply condensed.epi_to_Condensed_map _ cβ hcβ,
    apply exact_with_constant_extend_zero_right,
    intro S,
    apply_with exact_with_constant_of_epi { instances := ff },
    swap, { exact H3b S },
    rw AddCommGroup.epi_iff_surjective,
    exact H3a S },
  { simp only [condensify_nonstrict, nonstrict_extend, whisker_right_comp,
      nat_trans.comp_app, category.assoc],
    erw [category.comp_id],
    repeat { apply exact_of_iso_comp_exact; [apply_instance, skip] },
    apply condensed.exact_of_exact_with_constant _ _ cα hcα,
    apply exact_with_constant_extend,
    intro S,
    refine ⟨_, _⟩,
    { ext x, specialize H2a S, apply_fun (λ φ, φ.to_fun) at H2a, exact congr_fun H2a x },
    { intros c' y hy,
      obtain ⟨x, hx, rfl⟩ := H2b S c' hy,
      refine ⟨@rescale.of c _ x, hx, rfl⟩, } }
end
.

-- move me
attribute [simps] Ab.ulift

lemma condensify_nonstrict_Tinv2 (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  condensify_nonstrict (Tinv2_nat_trans F) (r'⁻¹ + 2) (Tinv2_bound_by F) =
  condensify_Tinv F - 2 • 𝟙 _ :=
begin
  delta Tinv2_nat_trans,
  rw [condensify_nonstrict_map_sub _ _ r'⁻¹ 2 (r'⁻¹ + 2) (Tinv_bound_by _) (twoid_bound_by _),
    condensify_nonstrict_map_nsmul _ 1 2, condensify_nonstrict_Tinv],
  swap,
  { intro, exact comphaus_filtered_pseudo_normed_group_hom.mk_of_bound_bound_by _ 1 _ },
  rw [← condensify_map_id],
  sorry
end
