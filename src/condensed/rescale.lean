import condensed.ab
import rescale.pseudo_normed_group

.

noncomputable theory

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
