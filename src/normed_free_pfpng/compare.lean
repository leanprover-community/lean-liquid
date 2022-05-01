import normed_free_pfpng.basic
import free_pfpng.basic
import condensed.exact
import condensed.condensify

open_locale nnreal big_operators

variables (p : ℝ≥0) (S : Fintype)
variables [fact (0 < p)] [fact (p ≤ 1)]

lemma nnnorm_int_rpow_le (n : ℤ) : ∥n∥₊ ^ (p : ℝ) ≤ ∥n∥₊ :=
begin
  have h0p : 0 < p := fact.out _,
  have hp1 : p ≤ 1 := fact.out _,
  rcases (eq_or_ne (∥n∥₊) 0) with (h|h),
  { simp only [h, le_zero_iff, nnreal.rpow_eq_zero_iff, eq_self_iff_true,
      ne.def, nnreal.coe_eq_zero, true_and],
    exact h0p.ne' },
  refine (nnreal.rpow_le_rpow_of_exponent_le _ hp1).trans _,
  swap, { rw [nnreal.coe_one, nnreal.rpow_one] },
  rw [← nnreal.coe_nat_abs] at h ⊢,
  norm_cast at h ⊢,
  exact nat.one_le_of_lt (ne.bot_lt h)
end

def free_pfpng_to_normed_free_pfpng :
  free_pfpng_functor ⟶ normed_free_pfpng_functor p :=
{ app := λ S,
  { to_fun := λ f, f,
    map_zero' := rfl,
    map_add' := λ _ _, rfl,
    strict' := begin
      have h0p : 0 < p := fact.out _,
      have hp1 : p ≤ 1 := fact.out _,
      rintro c f (hf : _ ≤ _),
      refine le_trans (finset.sum_le_sum _) hf,
      rintro s -,
      exact nnnorm_int_rpow_le p _,
    end,
    continuous' := λ c, continuous_of_discrete_topology },
  naturality' := by { intros S T f, ext φ t, refl } }
.

open category_theory

noncomputable
def cond_free_pfpng_to_normed_free_pfpng :
  condensify (free_pfpng_functor ⋙ PFPNG₁_to_CHFPNG₁ₑₗ) ⟶
  condensify (normed_free_pfpng_functor p ⋙ PFPNG₁_to_CHFPNG₁ₑₗ) :=
condensify_map $ whisker_right (free_pfpng_to_normed_free_pfpng p) _

open CompHausFiltPseuNormGrp₁

-- move me
lemma condensify_map_zero (F G : Fintype ⥤ CompHausFiltPseuNormGrp₁) :
  condensify_map (0 : F ⟶ G) = 0 :=
begin
  delta condensify_map condensify_nonstrict,
  suffices : nonstrict_extend
    (whisker_right (0 : F ⟶ G) CHFPNG₁_to_CHFPNGₑₗ) 1 _ = 0,
  { rw this, refl, },
  rw [nonstrict_extend_whisker_right_enlarging,
    Profinite.extend_nat_trans_zero],
  refl,
end

instance (S : Profinite) : mono ((cond_free_pfpng_to_normed_free_pfpng p).app S) :=
begin
  simp only [cond_free_pfpng_to_normed_free_pfpng, condensify_map, condensify_nonstrict],
  rw nonstrict_extend_whisker_right_enlarging,
  apply condensed.mono_to_Condensed_map,
  apply exact_with_constant_extend_zero_left,
  intro S,
  apply_with exact_with_constant_of_mono { instances := ff },
  rw [AddCommGroup.mono_iff_injective, injective_iff_map_eq_zero],
  intros f hf,
  exact hf,
end

instance (S : Profinite) : epi ((cond_free_pfpng_to_normed_free_pfpng p).app S) :=
begin
  simp only [cond_free_pfpng_to_normed_free_pfpng, condensify_map, condensify_nonstrict],
  rw nonstrict_extend_whisker_right_enlarging,
  let κ : ℝ≥0 → ℝ≥0 := λ c, max c (c ^ (p⁻¹ : ℝ)),
  have hκ : id ≤ κ := λ c, le_max_left _ _,
  apply condensed.epi_to_Condensed_map _ κ,
  apply exact_with_constant_extend_zero_right,
  intro S,
  apply exact_with_constant_of_epi _ _ _ hκ,
  intros c f hf,
  refine ⟨f, _, rfl⟩,
  change ∑ _, _ ≤ _ at hf,
  show ∑ _, _ ≤ _,
  have h0p : 0 < p := fact.out _,
  have hp1 : p ≤ 1 := fact.out _,
  have h0pinv : 0 ≤ p⁻¹, { rw ← nnreal.inv_pos at h0p, exact h0p.le },
  have := (nnreal.rpow_sum_le_sum_rpow _ _ h0p hp1).trans hf,
  replace this := nnreal.rpow_le_rpow this h0pinv,
  rw [← nnreal.rpow_mul, ← nnreal.coe_mul, mul_inv_cancel h0p.ne',
    nnreal.coe_one, nnreal.rpow_one] at this,
  exact this.trans (le_max_right _ _),
end

instance (S : Profinite) : is_iso ((cond_free_pfpng_to_normed_free_pfpng p).app S) :=
is_iso_of_mono_of_epi _
