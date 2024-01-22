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

open ProFiltPseuNormGrpWithTinv₁ CompHausFiltPseuNormGrp₁ CompHausFiltPseuNormGrp

variables {r'}

/--
Given a functor `F` from `Fintype` to `CompHausFiltPseuNormGrp₁`, we can obtain
a functor `Profinite ⥤ CompHausFiltPseuNormGrp₁` by expressing any profinite
set as a limit of finite sets and taking a limit in the target category.
We then compose with the functor to condensed abelian groups, and the result is
called `condensify F`.
-/
def condensify (F : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
(Profinite.extend.{u} F ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u}) ⋙ to_Condensed.{u}

variables {F G H : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}}
variables (α β : F ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u} ⟶ G ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u})
variables (c cα cβ cαβ : ℝ≥0) [fact (0 < c)]  [fact (0 < cα)] [fact (0 < cβ)] [fact (0 < cαβ)]

/--
Given functors `F G : Fintype ⥤ CompHausFiltPseuNormGrp₁` and a
natural transformation `η` between the induced functors `Fintype ⥤ CompHausFiltPseuNormGrp`
(obtained by composing with `CHFPNG₁_to_CHFPNGₑₗ`), such that the components of `η` are bounded
by a *single* `c : ℝ≥0`, this is the morphism between the associated condensed abelian groups.
-/
def condensify_nonstrict
  (α : F ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u} ⟶ G ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u}) (c : ℝ≥0) [fact (0 < c)]
  (h : ∀ X, (α.app X).bound_by c) :
  condensify F ⟶ condensify G :=
whisker_right (nonstrict_extend.{u} α c h) to_Condensed

lemma condensify_nonstrict_id (c : ℝ≥0) [fact (0 < c)]
  (h : ∀ X, (nat_trans.app (𝟙 (F ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u})) X).bound_by c) :
  condensify_nonstrict (𝟙 _) c h = 𝟙 _ :=
by { simp only [condensify_nonstrict, nonstrict_extend_id, whisker_right_id'], refl }

lemma condensify_nonstrict_comp
  (α : F ⋙ CHFPNG₁_to_CHFPNGₑₗ ⟶ G ⋙ CHFPNG₁_to_CHFPNGₑₗ)
  (β : G ⋙ CHFPNG₁_to_CHFPNGₑₗ ⟶ H ⋙ CHFPNG₁_to_CHFPNGₑₗ)
  (hα : ∀ X, (α.app X).bound_by cα) (hβ : ∀ X, (β.app X).bound_by cβ)
  (hαβ : ∀ X, ((α ≫ β).app X).bound_by cαβ) :
  condensify_nonstrict (α ≫ β) cαβ hαβ =
    condensify_nonstrict α cα hα ≫ condensify_nonstrict β cβ hβ :=
begin
  simp only [condensify_nonstrict, whisker_right_comp],
  rw [nonstrict_extend_comp cα cβ cαβ _ _ _ _, whisker_right_comp],
end

def condensify_map (α : F ⟶ G) : condensify F ⟶ condensify G :=
condensify_nonstrict (whisker_right α _) 1
  (λ X, (comphaus_filtered_pseudo_normed_group_hom.mk_of_strict_strict _ _).bound_by_one)

lemma condensify_map_id (F : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  condensify_map (𝟙 F) = 𝟙 (condensify F) :=
condensify_nonstrict_id _ _

lemma condensify_map_comp (α : F ⟶ G) (β : G ⟶ H) :
  condensify_map (α ≫ β) = condensify_map α ≫ condensify_map β :=
begin
  dsimp only [condensify_map],
  simp only [whisker_right_comp],
  apply condensify_nonstrict_comp,
end

def condensify_def (F : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  condensify F ≅ Profinite.extend.{u} F ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u} ⋙ to_Condensed.{u} :=
iso.refl _

/-- Given a family `F` of profinitely filtered normed groups with `T⁻¹`,
  indexed by a category (and such that all the morphisms in the family are strict),
  `Tinv_nat_trans` is the associated (possibly non-strict) morphism from the
  corresponding family of `CompHaus`ly filtered pseudo-normed groups coming from `T⁻¹`.
  -/
def Tinv_nat_trans (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  (F ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ.{u} r') ⋙ CHFPNG₁_to_CHFPNGₑₗ ⟶
  (F ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ.{u} r') ⋙ CHFPNG₁_to_CHFPNGₑₗ :=
{ app := λ X, profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv,
  naturality' := λ X Y f, by { ext x, exact ((F.map f).map_Tinv x).symm } }

/-- The endomorphism `T⁻¹ - 2` of a strict family of profinitely-filtered
pseudo-normed groups with `T⁻¹`, considered as a possibly non-strict
endomorphism of the associated `CompHaus`ly filtered pseudo-normed groups. -/
def Tinv2_nat_trans (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  (F ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ.{u} r') ⋙ CHFPNG₁_to_CHFPNGₑₗ ⟶
  (F ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ.{u} r') ⋙ CHFPNG₁_to_CHFPNGₑₗ :=
Tinv_nat_trans F - 2 • 𝟙 _

lemma Tinv_bound_by (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') (X : C) :
  ((Tinv_nat_trans F).app X).bound_by r'⁻¹ :=
profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv_bound_by

lemma twoid_bound_by (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') (X : C) :
  comphaus_filtered_pseudo_normed_group_hom.bound_by
    ((2 • 𝟙 ((F ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r') ⋙ CHFPNG₁_to_CHFPNGₑₗ)).app X) 2 :=
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
  Tinv_nat_trans F ≫ @whisker_right _ _ _ _ _ _ F G α (PFPNGT₁_to_CHFPNG₁ₑₗ r' ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u}) =
  @whisker_right _ _ _ _ _ _ F G α (PFPNGT₁_to_CHFPNG₁ₑₗ r' ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u}) ≫ Tinv_nat_trans G :=
by { ext X x, exact (α.app X).map_Tinv x }

-- move me
instance fact_inv_pos : fact (0 < r'⁻¹) := ⟨nnreal.inv_pos.2 $ fact.out _⟩

--set_option pp.universes true

/--
Given a functor from `Fintype` to `ProFiltPseuNormGrpWithTinv₁`, the `T⁻¹` action
is a nonstrict morphism which is natural (see `Tinv_nat_trans`) and thus
induces a morphism on the associated condensed abelian groups.
-/
def condensify_Tinv (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  condensify.{u} (F ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r') ⟶ condensify.{u} (F ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r') :=
condensify_nonstrict (Tinv_nat_trans _) r'⁻¹ (Tinv_bound_by _)

/--
A variant of `condensify_Tinv` with a different bound, given by `r'⁻¹ + 2`.
-/
def condensify_Tinv2 (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  condensify.{u} (F ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r') ⟶ condensify.{u} (F ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r') :=
condensify_nonstrict (Tinv2_nat_trans _) (r'⁻¹ + 2) (Tinv2_bound_by _)

lemma condensify_map_comp_Tinv {F G : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r'}
  (α : F ⟶ G) :
  condensify_map (whisker_right α (PFPNGT₁_to_CHFPNG₁ₑₗ r')) ≫ condensify_Tinv G =
  condensify_Tinv F ≫ condensify_map (whisker_right α (PFPNGT₁_to_CHFPNG₁ₑₗ r')) :=
begin
  delta condensify_map condensify_Tinv,
  rw [← condensify_nonstrict_comp 1 r'⁻¹ r'⁻¹, ← condensify_nonstrict_comp r'⁻¹ 1 r'⁻¹],
  swap, {
    intro X,
    rw nat_trans.comp_app,
    rw ← one_mul r'⁻¹,
    apply comphaus_filtered_pseudo_normed_group_hom.bound_by.comp (Tinv_bound_by F X),
    simp only [whisker_right_twice, whisker_right_app, functor.comp_map, CHFPNG₁_to_CHFPNGₑₗ_map],
    apply strict_comphaus_filtered_pseudo_normed_group_hom.to_chfpsng_hom.bound_by_one
    },
  swap, {
    intro X,
    rw nat_trans.comp_app,
    rw ← mul_one r'⁻¹,
    refine comphaus_filtered_pseudo_normed_group_hom.bound_by.comp _ (Tinv_bound_by G X),
    simp only [whisker_right_twice, whisker_right_app, functor.comp_map, CHFPNG₁_to_CHFPNGₑₗ_map],
    apply strict_comphaus_filtered_pseudo_normed_group_hom.to_chfpsng_hom.bound_by_one, },
  { simp only [whisker_right_twice, Tinv_nat_trans_comp], },
end
.

section


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

-- lemma nonstrict_extend_Tinv (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
--   nonstrict_extend (Tinv_nat_trans F) r'⁻¹ (Tinv_bound_by _) =
--     nat_trans.conj_by (iso_whisker_right
--       (Profinite.extend_commutes F (PFPNG₁_to_CHFPNG₁ₑₗ.{u} r')).symm enlarging_functor.{u})
--         (Tinv_nat_trans (Profinite.extend F)) :=
-- begin
--   refine nonstrict_extend_ext' _ _ r'⁻¹ (nonstrict_extend_bound_by _ _ _) _ _,
--   { admit },
--   { rw [nonstrict_extend_whisker_left],
--     simp only [whisker_left_comp, ← iso_whisker_left_hom, ← iso_whisker_left_inv,
--       ← iso.inv_comp_eq, iso.eq_comp_inv, category.assoc],
--     admit }
-- end

lemma condensify_nonstrict_Tinv (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  condensify_nonstrict (Tinv_nat_trans F) r'⁻¹ (Tinv_bound_by _) = condensify_Tinv F :=
rfl

lemma condensify_nonstrict_whisker_right_enlarging (α : F ⟶ G) :
  condensify_nonstrict (whisker_right α _) 1
    (λ X, (comphaus_filtered_pseudo_normed_group_hom.mk_of_strict_strict _ _).bound_by_one) =
  condensify_map α :=
rfl

end

open pseudo_normed_group (filtration)

lemma exact_of_iso_comp_exact {V : Type u} [category V] [limits.has_images V]
  [limits.has_zero_morphisms V] [limits.has_equalizers V]
  {A B C D : V} (f : A ⟶ B) {g : B ⟶ C} {h : C ⟶ D} (hf : is_iso f) (hgh : exact g h) :
  exact (f ≫ g) h :=
by rwa exact_iso_comp

lemma condensify_nonstrict_exact
  (α : F ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u} ⟶ G ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u}) (β : G ⟶ H)
  (c : ℝ≥0) [fact (0 < c)]
  (h : ∀ X, (α.app X).bound_by c)
  (cα cβ : ℝ≥0 → ℝ≥0) (hcα : id ≤ cα) (hcβ : id ≤ cβ)
  (H1 : ∀ S, function.injective (α.app S))
  (H2a : ∀ S, (α.app S) ≫ ((whisker_right β _).app S) = 0)
  (H2b : ∀ S c', (β.app S) ⁻¹' {0} ∩ filtration (G.obj S) c' ⊆
    (α.app S) '' filtration (F.obj S) (cα c' * c⁻¹))
  (H3b : ∀ S c', filtration (H.obj S) c' ⊆ (β.app S) '' filtration (G.obj S) (cβ c'))
  (X : Profinite.{u}) :
  short_exact ((condensify_nonstrict α c h).app X) ((condensify_map β).app X) :=
begin
  apply_with short_exact.mk { instances := ff },
  { simp only [condensify_nonstrict, nonstrict_extend, whisker_right_comp],
    repeat { apply_with mono_comp { instances := ff }; try { apply_instance } },
    apply Condensed.mono_to_Condensed_map,
    apply strongly_exact_extend_zero_left,
    intro S,
    apply_with strongly_exact_of_mono { instances := ff },
    rw AddCommGroup.mono_iff_injective,
    exact H1 S, },
  { dsimp only [condensify_map, condensify_nonstrict],
    rw nonstrict_extend_whisker_right_enlarging,
    apply Condensed.epi_to_Condensed_map _ cβ,
    apply strongly_exact_extend_zero_right,
    intro S,
    apply strongly_exact_of_epi _ _ _ hcβ (H3b S), },
  { dsimp only [condensify_map, condensify_nonstrict],
    rw nonstrict_extend_whisker_right_enlarging,
    simp only [nonstrict_extend, whisker_right_comp, nat_trans.comp_app, category.assoc],
    repeat { apply exact_of_iso_comp_exact; [apply_instance, skip] },
    apply Condensed.exact_of_strongly_exact _ _ cα,
    apply strongly_exact.extend,
    intro S,
    refine ⟨_, _, hcα⟩,
    { ext x, specialize H2a S, apply_fun (λ φ, φ.to_fun) at H2a, exact congr_fun H2a x },
    { intros c' y hy,
      obtain ⟨x, hx, rfl⟩ := H2b S c' hy,
      refine ⟨@rescale.of c _ x, hx, rfl⟩, } }
end
.

lemma condensify_exact (α : F ⟶ G) (β : G ⟶ H)
  (cα cβ : ℝ≥0 → ℝ≥0) (hcα : id ≤ cα) (hcβ : id ≤ cβ)
  (H1 : ∀ S, function.injective (α.app S))
  (H2a : ∀ S, α.app S ≫ β.app S = 0)
  (H2b : ∀ S c, (β.app S) ⁻¹' {0} ∩ filtration (G.obj S) c ⊆
    (α.app S) '' filtration (F.obj S) (cα c))
  (H3b : ∀ S c, filtration (H.obj S) c ⊆ (β.app S) '' filtration (G.obj S) (cβ c))
  (X : Profinite.{u}) :
  short_exact ((condensify_map α).app X) ((condensify_map β).app X) :=
begin
  refine condensify_nonstrict_exact _ _ 1 _ cα cβ hcα hcβ H1 _ _ H3b _,
  { intro S, simp only [whisker_right_app, ← functor.map_comp, H2a], refl, },
  { intros S c' x H, obtain ⟨x, hx, rfl⟩ := H2b S c' H,
    refine ⟨x, pseudo_normed_group.filtration_mono _ hx, rfl⟩,
    simp only [inv_one, mul_one], },
end

-- move me
attribute [simps] Ab.ulift

lemma condensify_Tinv2_eq (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
  condensify_Tinv2 F = condensify_Tinv F - 2 • 𝟙 _ :=
begin
  delta condensify_Tinv2 Tinv2_nat_trans,
  rw [condensify_nonstrict_map_sub _ _ r'⁻¹ 2 (r'⁻¹ + 2) (Tinv_bound_by _) (twoid_bound_by _),
    condensify_nonstrict_map_nsmul _ 1 2, condensify_nonstrict_Tinv],
  swap,
  { intro, exact comphaus_filtered_pseudo_normed_group_hom.mk_of_bound_bound_by _ 1 _ },
  rw [← condensify_map_id, ← condensify_nonstrict_whisker_right_enlarging],
  refl
end

open category_theory.preadditive

lemma condensify_map_comp_Tinv2 {F G : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r'}
  (α : F ⟶ G) :
  condensify_map (whisker_right α (PFPNGT₁_to_CHFPNG₁ₑₗ r')) ≫ condensify_Tinv2 G =
  condensify_Tinv2 F ≫ condensify_map (whisker_right α (PFPNGT₁_to_CHFPNG₁ₑₗ r')) :=
by simp only [condensify_Tinv2_eq, comp_sub, sub_comp, comp_nsmul, nsmul_comp,
    condensify_map_comp_Tinv, category.id_comp, category.comp_id]
