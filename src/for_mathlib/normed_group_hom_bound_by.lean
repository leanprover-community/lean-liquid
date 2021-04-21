import analysis.normed_space.normed_group_hom
import normed_group.NormedGroup

open_locale nnreal big_operators

namespace normed_group_hom

variables {V₁ V₂ V₃ : Type*} [semi_normed_group V₁] [semi_normed_group V₂] [semi_normed_group V₃]
variables {f : normed_group_hom V₁ V₂} {g : normed_group_hom V₂ V₃}

lemma bound_by.norm_noninc (hf : f.bound_by 1) : f.norm_noninc :=
λ v, (hf v).trans $ by rw [nnreal.coe_one, one_mul]

lemma bound_by.comp {C₁ C₂ : ℝ≥0} (hg : g.bound_by C₂) (hf : f.bound_by C₁) :
  (g.comp f).bound_by (C₂ * C₁) :=
λ v,
calc ∥g (f v)∥
    ≤ C₂ * ∥f v∥ : hg _
... ≤ C₂ * (C₁ * ∥v∥) : mul_le_mul le_rfl (hf _) (norm_nonneg _) C₂.coe_nonneg
... = (C₂ * C₁) * ∥v∥ : (mul_assoc _ _ _).symm

lemma bound_by.comp' (C₁ C₂ C₃ : ℝ≥0) (hC : C₃ = C₂ * C₁) (hg : g.bound_by C₂) (hf : f.bound_by C₁) :
  (g.comp f).bound_by C₃ :=
by { rw hC, exact hg.comp hf }

lemma zero_bound_by (C : ℝ≥0) : (0 : normed_group_hom V₁ V₂).bound_by C :=
λ v,
calc ∥(0 : V₂)∥ = 0       : norm_zero
            ... ≤ C * ∥v∥ : mul_nonneg C.coe_nonneg (norm_nonneg _)

lemma bound_by.le {C₁ C₂ : ℝ≥0} (hf : f.bound_by C₁) (h : C₁ ≤ C₂) :
  f.bound_by C₂ :=
λ v, (hf v).trans $ mul_le_mul h le_rfl (norm_nonneg _) C₂.coe_nonneg

lemma bound_by.add {f g : normed_group_hom V₁ V₂} {Cf Cg : ℝ≥0}
  (hf : f.bound_by Cf) (hg : g.bound_by Cg) :
  (f + g).bound_by (Cf + Cg) :=
begin
  intro v,
  rw [nnreal.coe_add, add_mul],
  calc ∥(f + g) v∥ ≤ ∥f v∥ + ∥g v∥ : norm_add_le _ _
  ... ≤ Cf * ∥v∥ + Cg * ∥v∥ : add_le_add (hf _) (hg _),
end

lemma bound_by.neg {f : normed_group_hom V₁ V₂} {Cf : ℝ≥0}
  (hf : f.bound_by Cf) :
  (-f).bound_by (Cf) :=
begin
  intro v,
  calc ∥(-f) v∥ = ∥f v∥ : norm_neg _
  ... ≤ Cf * ∥v∥ : hf _,
end

lemma bound_by.sum {ι : Type*} (s : finset ι)
  (f : ι → normed_group_hom V₁ V₂) (C : ι → ℝ≥0) (h : ∀ i ∈ s, (f i).bound_by (C i)) :
  (∑ i in s, f i).bound_by (∑ i in s, C i) :=
begin
  classical,
  revert h, apply finset.induction_on s; clear s,
  { intros, simp only [finset.sum_empty], exact zero_bound_by _ },
  { intros i s his IH h,
    simp only [finset.sum_insert his],
    exact (h i $ s.mem_insert_self _).add (IH $ λ i hi, h i $ finset.mem_insert_of_mem hi) }
end

@[simp] lemma bound_by.nat_smul {C : ℝ≥0} (hf : f.bound_by C) (n : ℕ) :
  (n • f).bound_by (n * C) :=
begin
  induction n with n ih,
  { simp only [nat.cast_zero, zero_mul, zero_smul], exact zero_bound_by _ },
  simp only [nat.succ_eq_add_one, add_smul, add_mul, nat.cast_add, nat.cast_one, one_mul, one_smul],
  exact ih.add hf
end

@[simp] lemma bound_by.int_smul {C : ℝ≥0} (hf : f.bound_by C) (n : ℤ) :
  (n • f).bound_by (n.nat_abs * C) :=
begin
  rw ← gsmul_eq_smul,
  induction n,
  { simp only [int.nat_abs_of_nat, int.of_nat_eq_coe, gsmul_coe_nat, nsmul_eq_smul],
    apply bound_by.nat_smul, exact hf },
  { apply bound_by.neg,
    show (↑(n+1) •ℤ f).bound_by (↑(-[1+ n].nat_abs) * C),
    simp only [gsmul_coe_nat, int.nat_abs, nsmul_eq_smul],
    apply bound_by.nat_smul, exact hf }
end

end normed_group_hom

namespace NormedGroup

universe variables u

variables {V₁ V₂ V₃ : NormedGroup.{u}} {f : V₁ ⟶ V₂} {g : V₂ ⟶ V₃}

lemma comp_bound_by (C₁ C₂ C₃ : ℝ≥0) (hC : C₃ = C₂ * C₁) (hf : f.bound_by C₁) (hg : g.bound_by C₂) :
  (f ≫ g).bound_by C₃ :=
hg.comp' _ _ _ hC hf

end NormedGroup
