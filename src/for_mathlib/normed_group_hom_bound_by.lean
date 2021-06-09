import analysis.normed_space.normed_group_hom
import for_mathlib.SemiNormedGroup

open_locale nnreal big_operators

namespace normed_group_hom

variables {V₁ V₂ V₃ : Type*} [semi_normed_group V₁] [semi_normed_group V₂] [semi_normed_group V₃]
variables {f : normed_group_hom V₁ V₂} {g : normed_group_hom V₂ V₃}

--This is in #7860
lemma norm_noninc_iff_norm_le_one : f.norm_noninc ↔ ∥f∥ ≤ 1 :=
begin
  refine ⟨λ h, _, λ h, λ v, _⟩,
  { refine op_norm_le_bound _ (zero_le_one) (λ v, _),
    simpa [one_mul] using h v },
  { simpa using le_of_op_norm_le f h v }
end

lemma sum.norm_le {ι : Type*} (s : finset ι)
  (f : ι → normed_group_hom V₁ V₂) (C : ι → ℝ) (h : ∀ i ∈ s, ∥f i∥ ≤ (C i)) :
  ∥(∑ i in s, f i)∥ ≤ (∑ i in s, C i) :=
begin
  classical,
  revert h, apply finset.induction_on s; clear s,
  { intros, simp only [norm_zero, finset.sum_empty] },
  { intros i s his IH h,
    simp only [finset.sum_insert his],
    refine le_trans (norm_add_le (f i) (finset.sum s f)) _,
    exact add_le_add (h i $ s.mem_insert_self _) (IH $ λ i hi, h i $ finset.mem_insert_of_mem hi) }
end

@[simp] lemma norm_nsmul_le {C : ℝ} (hf : ∥f∥ ≤ C) (n : ℕ) : ∥n • f∥ ≤ n * C :=
begin
  induction n with i hi,
  { simp only [norm_zero, nat.cast_zero, zero_mul, zero_smul] },
  simp only [nat.succ_eq_add_one, add_smul, add_mul, nat.cast_add, nat.cast_one, one_mul, one_smul],
  exact le_trans (norm_add_le _ _) (add_le_add hi hf),
end

@[simp] lemma norm_gsmul_le {C : ℝ} (hf : ∥f∥ ≤ C) (n : ℤ) : ∥n • f∥ ≤ (n.nat_abs * C) :=
begin
  induction n,
  { simp only [int.nat_abs_of_nat, int.of_nat_eq_coe, gsmul_coe_nat, nsmul_eq_smul],
    exact norm_nsmul_le hf n },
  { simp only [gsmul_neg_succ_of_nat, nat.cast_succ, int.nat_abs, norm_neg],
    exact norm_nsmul_le hf n.succ }
end

lemma norm_comp_le_of_le {C₁ C₂ : ℝ} (hg : ∥g∥ ≤ C₂) (hf : ∥f∥ ≤ C₁) :
  ∥g.comp f∥ ≤ C₂ * C₁ :=
le_trans (norm_comp_le g f) $ mul_le_mul hg hf (norm_nonneg _) (le_trans (norm_nonneg _) hg)

lemma norm_comp_le_of_le' (C₁ C₂ C₃ : ℝ) (h : C₃ = C₂ * C₁) (hg : ∥g∥ ≤ C₂) (hf : ∥f∥ ≤ C₁) :
  ∥g.comp f∥ ≤ C₃ :=
by { rw h, exact norm_comp_le_of_le hg hf }

end normed_group_hom

namespace SemiNormedGroup

universe variables u

variables {V₁ V₂ V₃ : SemiNormedGroup.{u}} {f : V₁ ⟶ V₂} {g : V₂ ⟶ V₃}

-- maybe prove this for `normed_group_hom` first, without the category lib
lemma coker.lift_norm_noninc {cond : f ≫ g = 0}
  (hg : g.norm_noninc) :
  (coker.lift cond).norm_noninc :=
normed_group_hom.norm_noninc_iff_norm_le_one.2 $ coker.norm_lift_le $
  normed_group_hom.norm_noninc_iff_norm_le_one.1 hg

end SemiNormedGroup
