import condensed.ab
import rescale.pseudo_normed_group
import hacks_and_tricks.asyncI
import for_mathlib.Profinite.extend
import facts.nnreal

.

noncomputable theory

universe u

open_locale nnreal
open category_theory

namespace comphaus_filtered_pseudo_normed_group

def strict_unscale (M : Type*) [comphaus_filtered_pseudo_normed_group M]
  (r : ℝ≥0) [fact (1 ≤ r)] :
  strict_comphaus_filtered_pseudo_normed_group_hom (rescale r M) M :=
{ to_fun := rescale.of.symm,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  strict' := λ c x hx, begin
    rw [rescale.mem_filtration] at hx,
    exact pseudo_normed_group.filtration_mono (fact.out _) hx,
  end,
  continuous' := λ c, @comphaus_filtered_pseudo_normed_group.continuous_cast_le M _ (c * r⁻¹) c _ }

end comphaus_filtered_pseudo_normed_group

namespace CompHausFiltPseuNormGrp

@[simps]
def rescale (r : ℝ≥0) : CompHausFiltPseuNormGrp ⥤ CompHausFiltPseuNormGrp :=
{ obj := λ M, of (rescale r M),
  map := λ M₁ M₂ f, rescale.map_comphaus_filtered_pseudo_normed_group_hom r f,
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }
.

def rescale_iso_component (r : ℝ≥0) [fact (0 < r)] (M : CompHausFiltPseuNormGrp) :
  (rescale r).obj M ≅ M :=
{ hom :=
  comphaus_filtered_pseudo_normed_group_hom.mk' (add_monoid_hom.id _)
  begin
    refine ⟨r⁻¹, λ c, ⟨_, _⟩⟩,
    { intros x hx,
      refine pseudo_normed_group.filtration_mono _ hx,
      rw mul_comm },
    { convert @comphaus_filtered_pseudo_normed_group.continuous_cast_le M _ _ _ _ using 1,
      rw mul_comm, apply_instance }
  end,
  inv :=
  comphaus_filtered_pseudo_normed_group_hom.mk' (add_monoid_hom.id _)
  begin
    have hr : r ≠ 0 := ne_of_gt (fact.out _),
    refine ⟨r, λ c, ⟨_, _⟩⟩,
    { intros x hx,
      dsimp, erw rescale.mem_filtration,
      refine pseudo_normed_group.filtration_mono _ hx,
      rw [mul_comm, inv_mul_cancel_left₀ hr], },
    { convert @comphaus_filtered_pseudo_normed_group.continuous_cast_le M _ _ _ _ using 1,
      rw [mul_comm, inv_mul_cancel_left₀ hr], apply_instance }
  end,
  hom_inv_id' := by { intros, ext, refl },
  inv_hom_id' := by { intros, ext, refl } }

def rescale_iso (r : ℝ≥0) [fact (0 < r)] : rescale r ≅ 𝟭 _ :=
nat_iso.of_components (rescale_iso_component r) $ λ _ _ _, rfl

-- instance (X : Profinite) (c : ℝ≥0) [fact (0 < c)] :
--   limits.preserves_limits (rescale c) :=
-- limits.preserves_limits_of_nat_iso (rescale_iso c).symm

instance rescale_preserves_limits_of_shape_discrete_quotient
  (X : Profinite.{u}) (c : ℝ≥0) [fact (0 < c)] :
  limits.preserves_limits_of_shape.{u u u u u+1 u+1} (discrete_quotient.{u} ↥X) (rescale.{u u} c) :=
limits.preserves_limits_of_shape_of_nat_iso (rescale_iso c).symm

def rescale₁ (r : ℝ≥0) [fact (0 < r)] (M : CompHausFiltPseuNormGrp)
  (exh : ∀ m : M, ∃ c, m ∈ pseudo_normed_group.filtration M c) :
  CompHausFiltPseuNormGrp₁ :=
{ M := _root_.rescale r M,
  exhaustive' := λ m, begin
    obtain ⟨c, hc⟩ := exh (rescale.of.symm m),
    simp only [rescale.mem_filtration],
    refine ⟨c * r, pseudo_normed_group.filtration_mono _ hc⟩,
    rw mul_inv_cancel_right₀, exact ne_of_gt (fact.out _),
  end }

end CompHausFiltPseuNormGrp

namespace CompHausFiltPseuNormGrp₁

@[simps]
def rescale (r : ℝ≥0) [fact (0 < r)] : CompHausFiltPseuNormGrp₁ ⥤ CompHausFiltPseuNormGrp₁ :=
{ obj := λ M,
  { M := rescale r M,
    exhaustive' := λ m, begin
      obtain ⟨c, hc⟩ := M.exhaustive (rescale.of.symm m),
      simp only [rescale.mem_filtration],
      refine ⟨c * r, pseudo_normed_group.filtration_mono _ hc⟩,
      rw mul_inv_cancel_right₀, exact ne_of_gt (fact.out _),
    end },
  map := λ M₁ M₂ f, rescale.map_strict_comphaus_filtered_pseudo_normed_group_hom r f,
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }
.

instance rescale_preserves_limits_of_shape_discrete_quotient
  (X : Profinite.{u}) (c : ℝ≥0) [fact (0 < c)] :
  limits.preserves_limits_of_shape.{u u u u u+1 u+1} (discrete_quotient.{u} ↥X) (rescale.{u u} c) :=
sorry

@[simps]
def rescale_enlarging_iso (r : ℝ≥0) [fact (0 < r)] :
  rescale r ⋙ enlarging_functor ≅ enlarging_functor :=
begin
  refine _ ≪≫ (iso_whisker_left _ (CompHausFiltPseuNormGrp.rescale_iso r))
    ≪≫ functor.right_unitor _,
  exact nat_iso.of_components (λ M, iso.refl _) (λ _ _ _, rfl),
end

@[simps]
def rescale_to_Condensed_iso (r : ℝ≥0) [fact (0 < r)] :
  rescale r ⋙ to_Condensed ≅
  enlarging_functor ⋙ CompHausFiltPseuNormGrp.rescale r ⋙ CompHausFiltPseuNormGrp.to_Condensed :=
nat_iso.of_components (λ M, iso.refl _) $ λ _ _ _, rfl

-- @[simps]
-- def strict_unscale (r : ℝ≥0) [fact (1 ≤ r)] :
--   rescale r ⟶ 𝟭 _ :=
-- { app := λ M, comphaus_filtered_pseudo_normed_group.strict_unscale M r,
--   naturality' := by { intros, ext, refl, } }

-- def Condensed_unscale (r : ℝ≥0) [fact (1 ≤ r)] :
--   rescale r ⋙ to_Condensed ⟶ to_Condensed :=
-- whisker_right (strict_unscale r) to_Condensed ≫ (functor.left_unitor _).hom

-- instance is_iso_strict_unscale (r : ℝ≥0) [fact (1 ≤ r)] (M) :
--   is_iso ((Condensed_unscale r).app M) :=
-- begin
--   admit
-- end

end CompHausFiltPseuNormGrp₁

namespace comphaus_filtered_pseudo_normed_group_hom

def strictify (M₁ M₂ : Type*)
  [comphaus_filtered_pseudo_normed_group M₁] [comphaus_filtered_pseudo_normed_group M₂]
  (f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂)
  (r : ℝ≥0) [fact (0 < r)]
  (hf : f.bound_by r) :
  strict_comphaus_filtered_pseudo_normed_group_hom (rescale r M₁) M₂ :=
strict_comphaus_filtered_pseudo_normed_group_hom.mk' (f.to_add_monoid_hom)
begin
  intro c,
  refine ⟨λ x hx, pseudo_normed_group.filtration_mono _ (hf hx), f.continuous _ (λ _, rfl)⟩,
  have hr : r ≠ 0 := ne_of_gt (fact.out _),
  rw [mul_left_comm, mul_inv_cancel hr, mul_one],
end

end comphaus_filtered_pseudo_normed_group_hom

open CompHausFiltPseuNormGrp₁

def strictify_nat_trans {C : Type*} [category C] {F G : C ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (α : F ⋙ enlarging_functor.{u} ⟶ G ⋙ enlarging_functor.{u}) (c : ℝ≥0) [fact (0 < c)]
  (h : ∀ X, (α.app X).bound_by c) :
  F ⋙ CompHausFiltPseuNormGrp₁.rescale.{u u} c ⟶ G :=
{ app := λ X, comphaus_filtered_pseudo_normed_group_hom.strictify _ _ (α.app X) c (h X),
  naturality' := λ X Y f, begin
    ext x, have := α.naturality f, apply_fun (λ φ, φ.to_fun x) at this, exact this
  end }

lemma strictify_nat_trans_enlarging {C : Type*} [category C]
  {F G : C ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (α : F ⋙ enlarging_functor.{u} ⟶ G ⋙ enlarging_functor.{u}) (c : ℝ≥0) [fact (0 < c)]
  (h : ∀ X, (α.app X).bound_by c) :
  whisker_right (strictify_nat_trans α c h) enlarging_functor =
  (functor.associator _ _ _).hom ≫ whisker_left F (rescale_enlarging_iso c).hom ≫ α :=
begin
  ext, refl,
end

@[simp]
lemma strictify_nat_trans_enlarging' {C : Type*} [category C]
  {F G : C ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (α : F ⋙ enlarging_functor.{u} ⟶ G ⋙ enlarging_functor.{u}) (c : ℝ≥0) [fact (0 < c)]
  (h : ∀ X, (α.app X).bound_by c) :
  whisker_left F (rescale_enlarging_iso.{u u} c).inv ≫ (functor.associator _ _ _).inv ≫
  whisker_right (strictify_nat_trans α c h) enlarging_functor = α :=
begin
  ext, refl,
end

-- move me
instance preadditive_CompHausFiltPseuNormGrp : preadditive CompHausFiltPseuNormGrp.{u} :=
{ hom_group := λ M N, by apply_instance,
  add_comp' := by { intros X Y Z f₁ f₂ g, ext, exact g.map_add _ _ },
  comp_add' := by { intros, ext, refl } }

section

variables {F G : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}}
variables (α β : F ⋙ enlarging_functor ⟶ G ⋙ enlarging_functor)
variables (c cα cβ cαβ : ℝ≥0) [fact (0 < c)] [fact (0 < cα)] [fact (0 < cβ)] [fact (0 < cαβ)]

def nonstrict_extend (α : F ⋙ enlarging_functor ⟶ G ⋙ enlarging_functor)
  (c : ℝ≥0) [fact (0 < c)] (h : ∀ X, (α.app X).bound_by c) :
  Profinite.extend.{u} F ⋙ enlarging_functor ⟶ Profinite.extend.{u} G ⋙ enlarging_functor :=
whisker_left (Profinite.extend F) (rescale_enlarging_iso.{u u} c).inv ≫
whisker_right ((Profinite.extend_commutes _ _).hom ≫
  Profinite.extend_nat_trans.{u} (strictify_nat_trans α c h)) enlarging_functor

-- move me
attribute [reassoc] whisker_left_comp whisker_right_comp

lemma nonstrict_extend_whisker_left (h : ∀ X, (α.app X).bound_by c) :
  whisker_left Fintype.to_Profinite (nonstrict_extend.{u} α c h) =
  (functor.associator _ _ _).inv ≫
  whisker_right (Profinite.extend_extends.{u} F).hom enlarging_functor.{u} ≫ α ≫
  whisker_right (Profinite.extend_extends.{u} G).inv enlarging_functor.{u} ≫
  (functor.associator _ _ _).hom :=
begin
  rw [nonstrict_extend, whisker_right_comp, whisker_left_comp, whisker_left_comp,
    ← whisker_right_left, ← whisker_right_left, Profinite.extend_nat_trans_whisker_left,
    whisker_right_comp, whisker_right_comp, strictify_nat_trans_enlarging,
    ← category_theory.whisker_right_comp_assoc, Profinite.extend_commutes_comp_extend_extends],
  refl,
end
.

lemma nonstrict_extend_bound_by (h : ∀ X, (α.app X).bound_by c) (X : Profinite.{u}) :
  ((nonstrict_extend α c h).app X).bound_by c :=
begin
  -- needs a `bound_by.comp` lemma
  sorry,
end

lemma nonstrict_extend_ext'
  (α β : Profinite.extend.{u} F ⋙ enlarging_functor ⟶ Profinite.extend G ⋙ enlarging_functor)
  (c : ℝ≥0) [fact (0 < c)] (hα : ∀ X, (α.app X).bound_by c) (hβ : ∀ X, (β.app X).bound_by c)
  (h : whisker_left Fintype.to_Profinite α = whisker_left Fintype.to_Profinite β) :
  α = β :=
begin
  suffices : strictify_nat_trans α c hα = strictify_nat_trans β c hβ,
  { rw [← strictify_nat_trans_enlarging' α c hα, ← strictify_nat_trans_enlarging' β c hβ, this] },
  rw ← cancel_epi (Profinite.extend_commutes F (CompHausFiltPseuNormGrp₁.rescale.{u u} c)).inv,
  apply Profinite.extend_nat_trans_ext,
  simp only [whisker_left_comp, cancel_epi],
  refine ((whiskering_right _ _ _).obj enlarging_functor.{u}).map_injective _,
  simp only [whiskering_right_obj_map, whisker_right_left,
    strictify_nat_trans_enlarging, whisker_left_comp, h],
end

-- move me
instance fact_max_pos : fact (0 < max cα cβ) := ⟨lt_max_iff.mpr (or.inl $ fact.out _)⟩

lemma nonstrict_extend_mono (c₁ c₂ : ℝ≥0) [fact (0 < c₁)] [fact (0 < c₂)]
  (h₁ : ∀ X, (α.app X).bound_by c₁) (h₂ : ∀ X, (α.app X).bound_by c₂) :
  nonstrict_extend α c₁ h₁ = nonstrict_extend α c₂ h₂ :=
begin
  refine nonstrict_extend_ext' _ _ (max c₁ c₂) _ _ _,
  { intro X, refine (nonstrict_extend_bound_by _ _ _ _).mono _ (le_max_left _ _), },
  { intro X, refine (nonstrict_extend_bound_by _ _ _ _).mono _ (le_max_right _ _), },
  { simp only [nonstrict_extend_whisker_left], }
end

lemma nonstrict_extend_ext
  (α β : Profinite.extend.{u} F ⋙ enlarging_functor ⟶ Profinite.extend G ⋙ enlarging_functor)
  (cα : ℝ≥0) [fact (0 < cα)] (cβ : ℝ≥0) [fact (0 < cβ)]
  (hα : ∀ X, (α.app X).bound_by cα) (hβ : ∀ X, (β.app X).bound_by cβ)
  (h : whisker_left Fintype.to_Profinite α = whisker_left Fintype.to_Profinite β) :
  α = β :=
begin
  refine nonstrict_extend_ext' _ _ (max cα cβ) _ _ h,
  { intro X, refine (hα X).mono _ (le_max_left _ _), },
  { intro X, refine (hβ X).mono _ (le_max_right _ _), },
end

-- move me
instance fact_add_pos (c₁ c₂ : ℝ≥0) [h₁ : fact (0 < c₁)] [h₂ : fact (0 < c₂)] :
  fact (0 < c₁ + c₂) :=
⟨add_pos h₁.1 h₂.1⟩

lemma nonstrict_extend_map_add (hα : ∀ X, (α.app X).bound_by cα) (hβ : ∀ X, (β.app X).bound_by cβ)
  (hαβ : ∀ X, ((α + β).app X).bound_by cαβ) :
  nonstrict_extend (α + β) cαβ hαβ = nonstrict_extend α cα hα + nonstrict_extend β cβ hβ :=
begin
  refine nonstrict_extend_ext _ _ cαβ (cα + cβ) _ _ _,
  { intro X, apply nonstrict_extend_bound_by, },
  { intro X,
    simp only [nat_trans.app_add],
    exact (nonstrict_extend_bound_by _ _ _ X).add (nonstrict_extend_bound_by _ _ _ X), },
  { ext S : 2,
    simp only [whisker_left_app, nat_trans.app_add],
    simp only [← whisker_left_app, nonstrict_extend_whisker_left,
      nonstrict_extend_whisker_left, preadditive.add_comp, preadditive.comp_add,
      nat_trans.app_add, nat_trans.comp_app, category.id_comp, category.comp_id,
      functor.associator_hom_app, functor.associator_inv_app], }
end

lemma nonstrict_extend_map_neg
  (hα : ∀ X, (α.app X).bound_by cα) (hβ : ∀ X, ((-α).app X).bound_by cβ) :
  nonstrict_extend (-α) cβ hβ = -nonstrict_extend α cα hα :=
begin
  refine nonstrict_extend_ext _ _ cβ cα _ _ _,
  { intro X, apply nonstrict_extend_bound_by, },
  { intro X, apply (nonstrict_extend_bound_by _ _ _ _).neg, },
  { ext S : 2,
    simp only [whisker_left_app, nat_trans.app_neg],
    simp only [← whisker_left_app, nonstrict_extend_whisker_left,
      nonstrict_extend_whisker_left, preadditive.neg_comp, preadditive.comp_neg,
      nat_trans.app_neg, nat_trans.comp_app, category.id_comp, category.comp_id,
      functor.associator_hom_app, functor.associator_inv_app], }
end

lemma nonstrict_extend_map_sub (hα : ∀ X, (α.app X).bound_by cα) (hβ : ∀ X, (β.app X).bound_by cβ)
  (hαβ : ∀ X, ((α - β).app X).bound_by cαβ) :
  nonstrict_extend (α - β) cαβ hαβ = nonstrict_extend α cα hα - nonstrict_extend β cβ hβ :=
begin
  refine nonstrict_extend_ext _ _ cαβ (cα + cβ) _ _ _,
  { intro X, apply nonstrict_extend_bound_by, },
  { intro X,
    simp only [nat_trans.app_sub],
    exact (nonstrict_extend_bound_by _ _ _ X).sub (nonstrict_extend_bound_by _ _ _ X), },
  { ext S : 2,
    simp only [whisker_left_app, nat_trans.app_sub],
    simp only [← whisker_left_app, nonstrict_extend_whisker_left,
      nonstrict_extend_whisker_left, preadditive.sub_comp, preadditive.comp_sub,
      nat_trans.app_sub, nat_trans.comp_app, category.id_comp, category.comp_id,
      functor.associator_hom_app, functor.associator_inv_app], },
end

lemma nonstrict_extend_map_nsmul (n : ℕ)
  (hα : ∀ X, (α.app X).bound_by cα) (hβ : ∀ X, ((n • α).app X).bound_by cβ) :
  nonstrict_extend (n • α) cβ hβ = n • nonstrict_extend α cα hα :=
begin
  refine nonstrict_extend_ext _ _ cβ (1 + n * cα) _ _ _,
  { intro X, apply nonstrict_extend_bound_by, },
  { intro X,
    simp only [nat_trans.app_nsmul],
    exact ((nonstrict_extend_bound_by _ _ _ _).nsmul _).mono _ le_add_self, },
  { ext S : 2,
    simp only [whisker_left_app, nat_trans.app_nsmul],
    simp only [← whisker_left_app, nonstrict_extend_whisker_left,
      nonstrict_extend_whisker_left, preadditive.nsmul_comp, preadditive.comp_nsmul,
      nat_trans.app_nsmul, nat_trans.comp_app, category.id_comp, category.comp_id,
      functor.associator_hom_app, functor.associator_inv_app], }
end

end
