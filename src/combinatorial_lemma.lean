import algebra.group.basic
import normed_group.NormedGroup

/-!
In this file we state and prove lemmas 9.7 and 9.8 of [Analytic].
-/

open_locale classical

section move_this

-- rewrite to include multiplicative version
def torsion_free (A : Type*) [add_comm_group A] : Prop :=
∀ (a : A) (n : ℕ), n • a = 0 → n = 0

-- do we have this in mathlib for mere groups (not modules)??
def finitely_generated (A : Type*) [add_comm_group A] : Prop :=
∃ s : finset A, ∀ a : A, a ∈ add_subgroup.closure (s : set A)

variables (Λ : Type*) [add_comm_group Λ]

--lemma findim {k V : Type*} [normed_field k] [normed_group V] [normed_space k V]
--  (fV : finitely_generated V)
--  {U : set V} (oU : is_open U) (U0 : (0 : V) ∈ U) {v : V} :
--  ∃ a : k, a • v ∈ U :=

open normed_field

lemma exists_ball_subset_open {V : Type*} [normed_group V] [normed_space ℝ V]
  {U : set V} (oU : is_open U) (U0 : (0 : V) ∈ U) (v : V) :
  ∃ a : ℝ, 0 < a ∧ metric.ball 0 a ⊆ U ∧ a • v ∈ U :=
begin
  rcases metric.is_open_iff.mp oU _ U0 with ⟨ε, e0, bU⟩,
  by_cases v0 : v = 0,
  { refine ⟨_, e0, bU, _⟩,
    rwa [v0, smul_zero] },
    refine ⟨(ε / 2) * (min ∥ v ∥⁻¹ 1), mul_pos (half_pos e0) _, _, _⟩,
    { exact lt_min ((inv_pos.mpr (norm_pos_iff.mpr v0))) zero_lt_one },
    { refine λ x hx, bU (set.mem_of_mem_of_subset hx (metric.ball_subset_ball _)),
      apply le_trans ((mul_le_iff_le_one_right (half_pos e0)).mpr _) (half_lt_self e0).le,
      exact min_le_right _ _ },
    { refine set.mem_of_mem_of_subset _ bU,
      rw [metric.mem_ball, dist_zero_right, norm_smul, norm_mul, mul_assoc],
      apply lt_of_le_of_lt _ (half_lt_self e0),
      unfold norm,
      rw [abs_of_pos (half_pos e0), abs_of_pos],
      apply (mul_le_iff_le_one_right (half_pos e0)).mpr,
      rw ← inv_inv (∥ v ∥),
      rw mul_inv_le_iff,
      have : min (∥v∥⁻¹) 1 * ∥v∥ ≤ 1 → min (∥v∥⁻¹) 1 ≤ 1 / ∥v∥,
      intros h,

      apply mul_le_one,
      exact (min_le_right _ _),
      exact norm_nonneg _,
      -- mul_assoc, norm_inv],
      rw [norm_norm, inv_mul_cancel, mul_one, norm_div, real.norm_two],
      refine lt_of_lt_of_le (half_lt_self (norm_pos_iff.mpr (ne_of_gt e0))) _,
      { unfold norm,
        rw abs_of_pos e0 },
      { rwa [ne.def, norm_eq_zero] } }
end

lemma exists_smul_mem_open {V : Type*} [normed_group V] [normed_space ℝ V]
  {U : set V} (oU : is_open U) (U0 : (0 : V) ∈ U) (v : V) :
  ∃ a : ℝ, 0 < a ∧ a • v ∈ U :=
begin
  by_cases v0 : v = 0,
  { refine ⟨_, zero_lt_one, _⟩,
    rwa [v0, smul_zero] },
  { rcases metric.is_open_iff.mp oU _ U0 with ⟨ε, e0, bU⟩,
    refine ⟨(ε / 2) * ∥ v ∥⁻¹, mul_pos (half_pos e0) (inv_pos.mpr (norm_pos_iff.mpr v0)), _⟩,
    { refine set.mem_of_mem_of_subset _ bU,
      rw [metric.mem_ball, dist_zero_right, norm_smul, norm_mul, mul_assoc, norm_inv],
      rw [norm_norm, inv_mul_cancel, mul_one, norm_div, real.norm_two],
      refine lt_of_lt_of_le (half_lt_self (norm_pos_iff.mpr (ne_of_gt e0))) _,
      { unfold norm,
        rw abs_of_pos e0 },
      { rwa [ne.def, norm_eq_zero] } } }
end

lemma exists_smul_finset_subset_open {V : Type*} [normed_group V] [normed_space ℝ V]
  {U : set V} (oU : is_open U) (U0 : (0 : V) ∈ U) (s : finset V) :
  ∃ a : ℝ, 0 < a ∧ ∀ v ∈ s, a • v ∈ U :=
begin
  apply finset.induction_on s,
  { refine ⟨_, zero_lt_one, _⟩,
    simp only [finset.not_mem_empty, forall_const, forall_prop_of_false, not_false_iff] },
  intros v s vs hs,
  rcases hs with ⟨e, e0, h⟩,
end

lemma lem97_nonneg (hΛ_tf : torsion_free Λ) (hΛ_fg : finitely_generated Λ)
  (N : ℕ) (s : finset Λ) :
  ∃ F : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∀ a ∈ s, 0 ≤ x a ∧ ∃ (x' ∈ F) (y : Λ →+ ℤ),
    x - x' = N • y ∧
    ∀ a ∈ s, 0 ≤ (x - x') a :=
begin
  sorry
end

/-- Lemma 9.7 of [Analytic]. -/
lemma lem97 (hΛ_tf : torsion_free Λ) (hΛ_fg : finitely_generated Λ)
  (N : ℕ) (s : finset Λ) :
  ∃ F : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ F) (y : Λ →+ ℤ),
    x - x' = N • y ∧
    ∀ a ∈ s, 0 ≤ x a ↔ 0 ≤ (x - x') a :=
begin

  sorry
end

end move_this
