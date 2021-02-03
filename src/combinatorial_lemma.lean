import algebra.group.basic
import analysis.convex.cone
import normed_group.NormedGroup
import Mbar.basic
import polyhedral_lattice

/-!
In this file we state and prove lemmas 9.7 and 9.8 of [Analytic].
-/

open_locale nnreal big_operators

section lem97

variables (Λ : Type*) [add_comm_group Λ]

--lemma findim {k V : Type*} [normed_field k] [normed_group V] [normed_space k V]
--  (fV : finitely_generated V)
--  {U : set V} (oU : is_open U) (U0 : (0 : V) ∈ U) {v : V} :
--  ∃ a : k, a • v ∈ U :=

open normed_field real set metric

lemma ball_scale_ball_out {X : Type*} [metric_space X] {x : X} {r s : ℝ} (hs : 0 < s) :
  ∃ a : ℝ, 0 < a ∧ ball x r ⊆ ball x (a * s) :=
begin
  by_cases r0 : r = 0,
  { rw [r0, ball_zero],
    exact ⟨_, zero_lt_one, empty_subset _⟩ },
  { refine ⟨ abs r / s, div_pos (abs_pos.mpr r0) hs, ball_subset_ball (le_trans (le_abs_self _) _)⟩,
    rw [div_mul_comm', div_self (ne_of_gt hs), one_mul] }
end

lemma ball_scale_ball_in {X : Type*} [metric_space X] (x : X) (r : ℝ) {s : ℝ} (hs : 0 < s) :
  ∃ a : ℝ, 0 < a ∧ ball x (a * r) ⊆ ball x s :=
begin
  by_cases r0 : r = 0,
  { conv { congr, funext, rw [r0, mul_zero, ball_zero] },
    exact ⟨_, zero_lt_one, empty_subset _⟩ },
  { refine ⟨ s / abs r, div_pos hs (abs_pos.mpr r0), ball_subset_ball (le_trans (le_abs_self _) _)⟩,
    rw [abs_mul, abs_div, abs_abs, div_mul_comm', div_self (ne_of_gt (abs_pos.mpr r0)), one_mul],
    exact le_of_eq (abs_of_pos hs) }
end

--@[simp] lemma norm_of_nonneg {a : ℝ} (ha : 0 ≤ a) : ∥ a ∥ = a :=
--by rw [norm_eq_abs, abs_of_nonneg ha]

lemma closed_ball_subset_ball {V : Type*} [metric_space V] (x : V) {a b : ℝ} (h : a < b) :
  closed_ball x a ⊆ ball x b :=
λ v hv, mem_ball.mpr $ lt_of_le_of_lt hv h

lemma scale_bounded_into_open {V : Type*} [normed_group V] [normed_space ℝ V]
  {U : set V} (oU : is_open U) (U0 : (0 : V) ∈ U) {s : set V} (bV : bounded s) :
  ∃ a b : ℝ, 0 < b ∧ ball 0 a ⊆ U ∧ ∀ v ∈ s, b • v ∈ ball (0 : V) a :=
begin
  rcases (bounded_iff_subset_ball 0).mp bV with ⟨N, sN⟩,
  rcases is_open_iff.mp oU _ U0 with ⟨ε, e0, bU⟩,
  by_cases N00 : N = 0,
  { subst N00,
    refine ⟨ε, 1, zero_lt_one, bU, λ v H, _⟩,
    rw [closed_ball_zero, subset_singleton_iff] at sN,
    rw [one_smul, (sN v H)],
    exact mem_ball_self e0 },
  by_cases N0 : N < 0,
  { refine ⟨-1, 1, zero_lt_one, _, _⟩,
    { rw ball_eq_empty_iff_nonpos.mpr (neg_nonpos.mpr (@zero_le_one ℝ _)),
      exact empty_subset _ },
    { rw [closed_ball_eq_empty_iff_neg.mpr N0] at sN,
      rw [(subset_empty_iff.mp sN)],
      rintros v ⟨⟩ } },
  obtain ⟨a, a0, H⟩ := ball_scale_ball_in (0 : V) (2 * N) e0,
  rw [← mul_assoc, mul_comm a] at H,
  refine ⟨ε, a / 2, half_pos a0, λ v vs, mem_of_mem_of_subset vs bU, λ v vs, mem_ball.mpr _⟩,
  rw [dist_zero_right, norm_smul, norm_of_nonneg (half_pos a0).le, mul_comm, ← mul_div_assoc],
  refine lt_of_le_of_lt _ (half_lt_self e0),
  rw [div_le_iff (@zero_lt_two ℝ _ _), div_mul_comm', div_self (@two_ne_zero ℝ _ _), one_mul],
  obtain F := sN vs,
  have : closed_ball 0 (a * N) ⊆ ball (0 : V) (2 * a * N),
  { refine closed_ball_subset_ball _ _,
    rw mul_assoc,
    refine (lt_mul_iff_one_lt_left (mul_pos a0 _)).mpr one_lt_two,
    exact lt_iff_le_and_ne.mpr ⟨not_lt.mp N0, ne.symm N00⟩ },
  rw [mul_comm, ← abs_of_pos a0, ← norm_eq_abs, ← norm_smul a v, ← dist_zero_right],
  refine mem_closed_ball.mp (mem_of_mem_of_subset (mem_of_mem_of_subset
    (mem_of_mem_of_subset _ this) H) ball_subset_closed_ball),
  rw [mem_closed_ball, dist_zero_right, norm_smul, norm_eq_abs, abs_of_pos a0],
  refine mul_le_mul le_rfl _ (norm_nonneg _) a0.le,
  rw ← dist_zero_right,
  exact mem_closed_ball.mpr (sN vs),
end


lemma scale_bounded_into_open {V : Type*} [normed_group V] [normed_space ℝ V]
  {U : set V} (oU : is_open U) (U0 : (0 : V) ∈ U) {s : set V} (bV : metric.bounded s) :
  ∃ a : ℝ, 0 < a ∧ metric.ball 0 a ⊆ U ∧ ∀ v ∈ s, a • v ∈ metric.ball (0 : V) a :=
begin
  rcases (bounded_iff_subset_ball 0).mp bV with ⟨N, sN⟩,
  rcases is_open_iff.mp oU _ U0 with ⟨ε, e0, bU⟩,
  have a1 : 1 ≤ abs N + 1 := (le_add_iff_nonneg_left _).mpr (abs_nonneg _),
  have a0 : 0 < abs N + 1 := lt_of_le_of_lt (abs_nonneg N) (lt_add_one (abs N)),
  refine ⟨ε / (abs N + 1), div_pos e0 a0, _, _⟩,
  { exact (λ x hx, mem_of_mem_of_subset (metric.ball_subset_ball
      ((div_le_iff a0).mpr ((le_mul_iff_one_le_right e0).mpr a1)) hx) bU) },
  { refine λ v vs, _,

    --refine λ v vs, mem_of_mem_of_subset (mem_ball_iff_norm.mpr _) bU,
    rw [sub_zero, norm_smul, norm_div, norm_of_nonneg (le_of_lt e0), norm_of_nonneg a0.le,
      div_mul_comm'],
    nth_rewrite 1 ← one_mul ε,
    refine mul_lt_mul ((div_lt_one _).mpr _) le_rfl e0 zero_le_one,
    { exact lt_of_le_of_lt (abs_nonneg N) (lt_add_one (abs N)) },
    { refine lt_of_le_of_lt _ (lt_of_le_of_lt (le_abs_self N) (lt_add_one (abs N))),
      rw ← sub_zero v,
      exact mem_closed_ball_iff_norm.mp (sN vs) } }
end

lemma scale_bounded_into_open_ball_conclusion {V : Type*} [normed_group V] [normed_space ℝ V]
  {U : set V} (oU : is_open U) (U0 : (0 : V) ∈ U) {s : set V} (bV : metric.bounded s) :
  ∃ a : ℝ, 0 < a ∧ metric.ball 0 a ⊆ U ∧ ∀ v ∈ s, a • v ∈ U :=
begin
  rcases (bounded_iff_subset_ball 0).mp bV with ⟨N, sN⟩,
  rcases is_open_iff.mp oU _ U0 with ⟨ε, e0, bU⟩,
  have a1 : 1 ≤ abs N + 1 := (le_add_iff_nonneg_left _).mpr (abs_nonneg _),
  have a0 : 0 < abs N + 1 := lt_of_le_of_lt (abs_nonneg N) (lt_add_one (abs N)),
  refine ⟨ε / (abs N + 1), div_pos e0 a0, _, _⟩,
  { exact (λ x hx, mem_of_mem_of_subset (metric.ball_subset_ball
      ((div_le_iff a0).mpr ((le_mul_iff_one_le_right e0).mpr a1)) hx) bU) },
  { refine λ v vs, mem_of_mem_of_subset (mem_ball_iff_norm.mpr _) bU,
    rw [sub_zero, norm_smul, norm_div, norm_of_nonneg (le_of_lt e0), norm_of_nonneg a0.le,
      div_mul_comm'],
    nth_rewrite 1 ← one_mul ε,
    refine mul_lt_mul ((div_lt_one _).mpr _) le_rfl e0 zero_le_one,
    { exact lt_of_le_of_lt (abs_nonneg N) (lt_add_one (abs N)) },
    { refine lt_of_le_of_lt _ (lt_of_le_of_lt (le_abs_self N) (lt_add_one (abs N))),
      rw ← sub_zero v,
      exact mem_closed_ball_iff_norm.mp (sN vs) } }
end


lemma exists_ball_subset_open {V : Type*} [normed_group V] [normed_space ℝ V]
  {U : set V} (oU : is_open U) (U0 : (0 : V) ∈ U) (v : V) :
  ∃ a : ℝ, 0 < a ∧ a • v ∈ U :=
begin
  obtain ⟨ε, e0, be, H⟩ := scale_bounded_into_open oU U0 (@bounded_singleton _ _ v),
  exact ⟨ε, e0, H v rfl⟩,
end

lemma exists_smul_mem_open {V : Type*} [normed_group V] [normed_space ℝ V]
  {U : set V} (oU : is_open U) (U0 : (0 : V) ∈ U) (v : V) :
  ∃ a : ℝ, 0 < a ∧ a • v ∈ U :=
begin
  rcases metric.is_open_iff.mp oU _ U0 with ⟨ε, e0, bU⟩,
  obtain F := exists_ball_subset_open oU U0 v,
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
  apply convex_cone,
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
lemma lem97 (hΛ_tf : torsion_free Λ) (hΛ_fg : module.finite ℤ Λ)
  (N : ℕ) (s : finset Λ) :
  ∃ F : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ F) (y : Λ →+ ℤ),
    x - x' = N • y ∧
    ∀ a ∈ s, 0 ≤ x a ↔ 0 ≤ (x - x') a :=
begin
  sorry
end

end lem97

open pseudo_normed_group

-- move this
namespace normed_group

instance (V : Type*) [normed_group V] : pseudo_normed_group V :=
{ filtration := λ c, {v | ∥v∥ ≤ c},
  filtration_mono := λ c₁ c₂ h v (hv : ∥v∥ ≤ c₁), le_trans hv h,
  zero_mem_filtration := λ c, by simp only [set.mem_set_of_eq, norm_zero, nnreal.zero_le_coe],
  neg_mem_filtration := λ c v hv, by simpa only [set.mem_set_of_eq, norm_neg] using hv,
  add_mem_filtration := λ c₁ c₂ v₁ v₂ hv₁ hv₂,
    calc ∥v₁ + v₂∥
        ≤ ∥v₁∥ + ∥v₂∥ : norm_add_le _ _
    ... ≤ c₁ + c₂ : add_le_add hv₁ hv₂ }

end normed_group

variables (Λ : Type*) (r' : ℝ≥0) (S : Type*)
variables [fintype S] [normed_group Λ] [polyhedral_lattice Λ]

instance foo : pseudo_normed_group (Mbar r' S) := by apply_instance

lemma lem98 (N : ℕ) (hn : 0 < N) :
  ∃ d, ∀ c (x : Λ →+ Mbar r' S) (hx : x ∈ filtration (Λ →+ Mbar r' S) c),
    ∃ y : fin N → (Λ →+ Mbar r' S),
      (∑ i, y i = x) ∧
      (∀ i, y i ∈ filtration (Λ →+ Mbar r' S) (c/N + d)) :=
begin
  sorry
end
