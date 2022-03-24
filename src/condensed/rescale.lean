import condensed.ab
import rescale.pseudo_normed_group
import hacks_and_tricks.asyncI
import for_mathlib.Profinite.extend

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

def nonstrict_extend {F G : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (α : F ⋙ enlarging_functor ⟶ G ⋙ enlarging_functor) (c : ℝ≥0) [fact (0 < c)]
  (h : ∀ X, (α.app X).bound_by c) :
  Profinite.extend.{u} F ⋙ enlarging_functor ⟶ Profinite.extend.{u} G ⋙ enlarging_functor :=
whisker_left (Profinite.extend F) (rescale_enlarging_iso.{u u} c).inv ≫
whisker_right ((Profinite.extend_commutes _ _).hom ≫
  Profinite.extend_nat_trans.{u} (strictify_nat_trans α c h)) enlarging_functor

-- move me
attribute [reassoc] whisker_left_comp whisker_right_comp

lemma nonstrict_extend_whisker_left {F G : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (α : F ⋙ enlarging_functor ⟶ G ⋙ enlarging_functor) (c : ℝ≥0) [fact (0 < c)]
  (h : ∀ X, (α.app X).bound_by c) :
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

lemma nonstrict_extend_ext {F G : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (α β : Profinite.extend.{u} F ⋙ enlarging_functor ⟶ Profinite.extend.{u} G ⋙ enlarging_functor)
  (c : ℝ≥0) [fact (0 < c)] (hα : ∀ X, (α.app X).bound_by c) (hβ : ∀ X, (β.app X).bound_by c)
  (h : whisker_left Fintype.to_Profinite α = whisker_left Fintype.to_Profinite β) :
  α = β :=
begin
  suffices : strictify_nat_trans α c hα = strictify_nat_trans β c hβ,
  { rw [← strictify_nat_trans_enlarging' α c hα, ← strictify_nat_trans_enlarging' β c hβ, this] },
  rw ← cancel_epi (Profinite.extend_commutes F (CompHausFiltPseuNormGrp₁.rescale.{u u} c)).inv,
  apply Profinite.extend_nat_trans_ext,
  simp only [whisker_left_comp, cancel_epi],
  -- move this
  haveI : faithful enlarging_functor.{u} := sorry,
  refine ((whiskering_right _ _ _).obj enlarging_functor.{u}).map_injective _,
  simp only [whiskering_right_obj_map],
  sorry
end
