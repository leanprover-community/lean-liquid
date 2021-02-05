import system_of_complexes

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes

variables (M M' N : system_of_complexes.{u}) (f : M ⟶ M') (g : M' ⟶ N)

/-- The normed snake lemma, weak version. See Proposition 9.10 from Analytic.pdf -/
--TODO Add the non weak version for complete system of complxes
lemma weak_normed_snake (k : ℝ≥0) (m : ℤ) (c₀ : ℝ≥0) [hk : fact (1 ≤ k)]
  (hf : ∀ c i, is_strict (f.apply : M.X c i ⟶ M'.X c i))
  (Hf : ∀ (c : ℝ≥0) (i : ℤ) (hi : i ≤ m + 1) (x : M.X (k * c) i),
    ∥(M.res x : M.X c i)∥ ≤ k * ∥f.apply x∥)
  (hg : ∀ c i, (g.apply : M'.X c i ⟶ N.X c i).ker = f.apply.range)
  (hgquot : system_of_complexes.is_quotient g)
  (hM : M.is_weak_bdd_exact_for_bdd_degree_above_idx k m c₀)
  (hM' : M'.is_weak_bdd_exact_for_bdd_degree_above_idx k m c₀)
--  (hM_adm : M.admissible)
  (hM'_adm : M'.admissible) :
  N.is_weak_bdd_exact_for_bdd_degree_above_idx (k ^ 3 + k) (m - 1) c₀ :=
begin
  intros c hc i hi norig ε hε,

  set c_new := k * (k * (k * c)) with hc_new,
  let ε₁ := ε/(↑k ^ 3 + 2 * ↑k + 1),

  haveI : fact (c_new ≤ (k ^ 3 + k) * c) := by
  { show k * (k * (k * c)) ≤ (k ^ 3 + k) * c,
    rw add_mul,
    convert (le_add_iff_nonneg_right (k^3 * c)).2 (zero_le') using 1,
    ring },
  set n := @res _ _ c_new _ _ norig with hn,
  haveI : fact (c ≤ c_new) :=
  calc c ≤ k * c             : le_mul_of_one_le_left' hk
     ... ≤ k * (k * c)       : le_mul_of_one_le_left' hk
     ... ≤ k * (k * (k * c)) : le_mul_of_one_le_left' hk,
  have honele : 1 ≤ k ^ 3 + 2 * k + 1, by {change fact _, apply_instance},
  have hzerok : ↑k ^ 3 + 2 * ↑k + 1 ≠ (0 : ℝ),
  { exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one honele) },
  have hε₁ : 0 < ε₁, by { refine div_pos hε (lt_of_lt_of_le zero_lt_one honele) },
  have hi3 : i + 1 + 1 + 1 ≤ m + 1 := by linarith,
  have hi1 : i + 1 < m := by linarith,
  have hkc : c₀ ≤ k * c := le_trans hc (le_mul_of_one_le_left' hk),
  letI kccnew : fact (k * c ≤ c_new),
  { rw hc_new,
    refine mul_le_mul (le_refl _) _ (zero_le _) (zero_le _),
    rw (show k * (k * c) = c * (k ^ 2), by ring),
    refine le_mul_of_le_of_one_le (le_refl _) _,
    change fact _,
    apply_instance },

  suffices hnorig : ∃ (y : (N.X c i)), ∥(N.res) n - (N.d) y∥ ≤ (k ^ 3 + k) * ∥N.d n∥ + ε,
  { refine Exists.imp _ hnorig,
    rintro a ha,
    simp only [res_res] at ha,
    calc _ ≤ _ : ha
       ... ≤ _ : _,
    simp only [hn, nnreal.coe_add, add_le_add_iff_right, nnreal.coe_pow],
    apply mul_le_mul_of_nonneg_left,
    { rw d_res,
      have hN_adm : N.admissible := admissible_of_quotient hgquot hM'_adm,
      convert hN_adm.res_norm_noninc _ _ _ _ (N.d norig) },
    { exact_mod_cast (nnreal.coe_nonneg (k ^ 3 + k)) } },

  obtain ⟨m', hm'⟩ := (hgquot _ _).surjective n,
  let m₁' := M'.d m',
  have hm₁' : g.apply m₁' = N.d n := by simpa [hm'] using (d_apply _ _ g m').symm,
  obtain ⟨m₁'', hm₁''⟩ := quotient_norm_lift (hgquot _ _) hε₁ (N.d n),
  have hm₁exist : ∃ m₁ : M.X _ _,  f.apply m₁ + m₁'' = m₁',
  { have hrange : m₁' - m₁'' ∈ f.apply.range,
    { rw [← hg _ _, mem_ker  _ _, map_sub, hm₁', hm₁''.1, sub_self] },
    obtain ⟨m₁, hm₁⟩ := (mem_range _ _).1 hrange,
    exact ⟨m₁, by rw [hm₁, sub_add_cancel]⟩ },
  obtain ⟨m₁, hm₁⟩ := hm₁exist,
  have hm₂ : f.apply (M.d m₁) = -(M'.d m₁''),
  { rw [← d_apply, eq_sub_of_add_eq hm₁, map_sub, ← coe_comp, d, d, homological_complex.d_squared,
      coe_zero, ← neg_inj, pi.zero_apply, zero_sub], },
  have hle := Hf _ _ hi3 (M.d m₁),
  rw [hm₂, norm_neg] at hle,
  replace hle := le_trans hle (mul_le_mul_of_nonneg_left (hM'_adm.d_norm_noninc _ _ m₁'')
    (le_trans zero_le_one hk)),
  replace hle := le_trans hle (mul_le_mul_of_nonneg_left (le_of_lt hm₁''.2)
    (le_trans zero_le_one hk)),
  obtain ⟨m₀, hm₀⟩ := hM _ hkc _ hi1 (M.res m₁) ε₁ hε₁,
  rw [res_res, d_res _] at hm₀,
  let mnew' := M'.res m' - f.apply m₀,
  let mnew₁' := M'.d mnew',
  have hmnew' : mnew₁' = M'.res m₁'' + f.apply (M.res m₁ - M.d m₀),
  { calc mnew₁' = M'.d (M'.res m' - f.apply m₀) : by refl
            ... = M'.res (M'.d m') - (f.apply (M.d m₀)) : by rw [map_sub, d_res _, d_apply]
            ... = M'.res (M'.d m') - (f.apply (M.res m₁)) +
              (f.apply (M.res m₁) - f.apply (M.d m₀)) : by abel
            ... = M'.res m₁'' + f.apply ((M.res m₁) - (M.d m₀)) : by
              rw [← map_sub, ← res_apply, ← map_sub, ← sub_eq_of_eq_add' hm₁.symm] },
  have hnormle : ∥mnew₁'∥ ≤ (∥N.d n∥ + ε₁) * (k ^ 2  + 1) + ε₁,
  { replace hm₀ := le_trans hm₀ (add_le_add_right (mul_le_mul_of_nonneg_left hle
      (@nnreal.zero_le_coe k)) ε₁),
    rw [← mul_assoc ↑k _ _] at hm₀,
    calc ∥mnew₁'∥ = ∥M'.res m₁'' + f.apply (M.res m₁ - M.d m₀)∥ : by rw [hmnew']
              ... ≤ ∥M'.res m₁''∥ + ∥f.apply (M.res m₁ - M.d m₀)∥ : norm_add_le _ _
              ... ≤ ∥m₁''∥ + ∥f.apply (M.res m₁ - M.d m₀)∥ : add_le_add_right
                (hM'_adm.res_norm_noninc _ _ _ kccnew m₁'') _
              ... = ∥m₁''∥ + ∥M.res m₁ - M.d m₀∥ : by rw [hf _ _ _]
              ... ≤ ∥N.d n∥ + ε₁ + ∥M.res m₁ - M.d m₀∥ : add_le_add_right (le_of_lt hm₁''.2)  _
              ... ≤ ∥N.d n∥ + ε₁ + (k * k * (∥N.d n∥ + ε₁) + ε₁) : add_le_add_left hm₀ _
              ... = (∥N.d n∥ + ε₁) * (k ^ 2  + 1) + ε₁ : by ring },
  obtain ⟨mnew₀, hmnew₀⟩ := hM' _ hc _ (lt_trans hi (sub_one_lt m)) mnew' _ hε₁,
  replace hmnew₀ := le_trans hmnew₀ (add_le_add_right (mul_le_mul_of_nonneg_left
    hnormle (@nnreal.zero_le_coe k)) ε₁),
  let nnew₀ := g.apply mnew₀,
  have hmnewlift : g.apply ((M'.res mnew') - (M'.d mnew₀)) = N.res n - N.d nnew₀,
  { suffices h : g.apply mnew' = N.res n,
    { rw [map_sub, ← res_apply, ← d_apply, h, res_res] },
    rw [map_sub],
    have hker : f.apply m₀ ∈ g.apply.ker,
    { rw [hg _ _, mem_range _ _],
      use m₀ },
    rw [(mem_ker _ _).1 hker, sub_zero, ← res_apply, hm'] },
  use nnew₀,
  rw [← hmnewlift],
  suffices : ∥M'.res mnew' - (M'.d) mnew₀∥ ≤ (k ^ 3 + k) * ∥N.d n∥ + ε,
  { exact le_trans (quotient_norm_le (hgquot _ _) (M'.res mnew' - (M'.d) mnew₀)) this },
  calc ∥(M'.res) mnew' - (M'.d) mnew₀∥ ≤ k * ((∥N.d n∥ + ε₁) * (k ^ 2 + 1) + ε₁) + ε₁ : hmnew₀
    ... = (k ^ 3 + k) * ∥N.d n∥ + (k ^ 3 + 2 * k + 1) * ε₁ : by ring
    ... = (k ^ 3 + k) * ∥N.d n∥ + (k ^ 3 + 2 * k + 1) * (ε / (↑k ^ 3 + 2 * ↑k + 1)) : by refl
    ... = (k ^ 3 + k) * ∥N.d n∥ + (k ^ 3 + 2 * k + 1) * ε / (k ^ 3 + 2 * k + 1) : by ring
    ... = (k ^ 3 + k) * ∥N.d n∥ + ε : by rw mul_div_cancel_left ε hzerok
end
