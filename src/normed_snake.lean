import system_of_complexes

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes

variables (M M' N : system_of_complexes.{u}) (f : M ⟶ M') (g : M' ⟶ N)

/-- The normed snake lemma, weak version. See Proposition 9.10 from Analytic.pdf -/
--TODO Add the non weak version for complete system of complexes
lemma weak_normed_snake {k k' k'' K K' K'' : ℝ≥0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')] [hk'' : fact (1 ≤ k'')]
  {m : ℤ} {c₀ : ℝ≥0}
  (hM : M.is_weak_bdd_exact_for_bdd_degree_above_idx k K m c₀)
  (hM' : M'.is_weak_bdd_exact_for_bdd_degree_above_idx k' K' m c₀)
  (hM'_adm : M'.admissible)
  (hf : ∀ c i, is_strict (f.apply : M.X c i ⟶ M'.X c i))
  (Hf : ∀ (c : ℝ≥0) (i : ℤ) (hi : i ≤ m + 1) (x : M.X (k'' * c) i),
    ∥(res x : M.X c i)∥ ≤ K'' * ∥f.apply x∥)
  (hg : ∀ c i, (g.apply : M'.X c i ⟶ N.X c i).ker = f.apply.range)
  (hgquot : system_of_complexes.is_quotient g) :
  N.is_weak_bdd_exact_for_bdd_degree_above_idx (k''*k*k') (K'*(K*K'' + 1)) (m - 1) c₀ :=
begin
  have bound_nonneg : (0 : ℝ) ≤ K' * (K * K'' + 1),
  { apply mul_nonneg nnreal.zero_le_coe,
    apply add_nonneg,
    exact_mod_cast nnreal.zero_le_coe,
    exact zero_le_one },
  intros c hc i hi,
  let c₁ := k'' * (k * (k' * c)),
  suffices : ∀ n : N.X c₁ (i + 1), ∀ ε > 0,
    ∃ y : N.X c i, ∥res n - d y∥ ≤ K' * (K * K'' + 1) * ∥d n∥ + ε,
  { dsimp [c₁] at this,
    intros n₁ ε hε,
    haveI hc : fact (k'' * k * k' * c = c₁) := by { show _ = _, dsimp [c₁], ring },
    let n : ↥(N.X c₁ (i + 1)) := res n₁,
    rcases this n ε hε with ⟨y, hy : ∥res (res n₁) - d y∥ ≤ K' * (K * K'' + 1) * ∥d (res n₁)∥ + ε⟩,
    rw [res_res, d_res] at hy,
    have : ∥(res (d n₁) : N.X (k'' * (k * (k' * c))) (i + 1 + 1)) ∥ ≤ ∥d n₁∥,
      by {apply (admissible_of_quotient hgquot hM'_adm).res_norm_noninc, },
    exact ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left this bound_nonneg) ε)⟩ },
  intros n ε hε,
  let ε₁ := ε/(K' * (K * K'' + 2) + 1),

  have honele : 1 ≤ K' * (K * K'' + 2) + 1, by { change fact _, apply_instance },
  have hε₁_ε : (K' * (K * K'' + 2) + 1 : ℝ)*ε₁ = ε,
    from mul_div_cancel' _ (by exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one honele)),
  have hε₁ : 0 < ε₁, from div_pos hε (lt_of_lt_of_le zero_lt_one honele),

  let c₁ := k''*(k*(k'*c)),
  obtain ⟨m' : M'.X c₁ (i + 1), hm' : g.apply m' = n⟩ := (hgquot _ _).surjective _,
  let m₁' := d m',
  have hm₁' : g.apply m₁' = d n := by simpa [hm'] using (d_apply _ _ g m').symm,
  obtain ⟨m₁'' : M'.X c₁ (i + 1 + 1), hgm₁'' : g.apply m₁'' = d n, hnorm_m₁'' : ∥m₁''∥ < ∥d n∥ + ε₁⟩
    := quotient_norm_lift (hgquot _ _) hε₁ (d n),
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : M.X c₁ (i + 1 + 1),  f.apply m₁ + m₁'' = m₁',
  { have hrange : m₁' - m₁'' ∈ f.apply.range,
    { rw [← hg _ _, mem_ker  _ _, map_sub, hm₁', hgm₁'', sub_self] },
    obtain ⟨m₁, hm₁⟩ := (mem_range _ _).1 hrange,
    exact ⟨m₁, by rw [hm₁, sub_add_cancel]⟩ },

  have hm₂ : f.apply (d m₁) = -d m₁'',
  { rw [← d_apply, eq_sub_of_add_eq hm₁, map_sub, ← coe_comp, d, d, homological_complex.d_squared,
      coe_zero, ← neg_inj, pi.zero_apply, zero_sub], },
  have hle : ∥res (d m₁)∥ ≤ K'' * ∥m₁''∥,
    calc ∥res (d m₁)∥ ≤ K'' * ∥f.apply (d m₁)∥ : Hf _ _ (by linarith) (d m₁)
                  ... = K'' * ∥d m₁''∥ : by rw [hm₂, norm_neg]
                  ... ≤ K'' * ∥m₁''∥ : (mul_le_mul_of_nonneg_left (hM'_adm.d_norm_noninc _ _ m₁'') $
                                                                  nnreal.coe_nonneg K''),
  obtain ⟨m₀ : M.X (k'*c) (i+1), hm₀ : ∥res (res m₁) - d m₀∥ ≤ K * ∥d (res m₁)∥ + ε₁⟩ :=
    hM _ (le_trans hc $ le_mul_of_one_le_left' hk') _ (by linarith) (res m₁) ε₁ hε₁,
  replace hm₀ : ∥res m₁ - d m₀∥ ≤ K * K'' * ∥d n∥ + K*K''*ε₁ + ε₁,
    calc ∥res m₁ - d m₀∥  = ∥res (res m₁) - d m₀∥ : by rw res_res
    ... ≤ K * ∥d (res m₁)∥ + ε₁ : hm₀
    ... = K * ∥res (d m₁)∥ + ε₁ : by rw d_res
    ... ≤ K*(K'' * ∥m₁''∥) + ε₁ : add_le_add_right (mul_le_mul_of_nonneg_left hle nnreal.zero_le_coe) _
    ... ≤ K*(K'' * (∥d n∥ + ε₁)) + ε₁ :  add_le_add_right (mul_le_mul_of_nonneg_left
                                        (mul_le_mul_of_nonneg_left hnorm_m₁''.le nnreal.zero_le_coe)
                                         nnreal.zero_le_coe) ε₁
    ... = K * K'' * ∥d n∥ + K*K''*ε₁ + ε₁ : by ring,

  let mnew' := res m' - f.apply m₀,
  let mnew₁' := d mnew',
  have hmnew' : mnew₁' = res m₁'' + f.apply (res m₁ - d m₀),
    calc mnew₁' = d (res m' - f.apply m₀) : rfl
            ... = res (d m') - (f.apply (d m₀)) : by rw [map_sub, d_res _, d_apply]
            ... = res (d m') - (f.apply (res m₁)) + (f.apply (res m₁) - f.apply (d m₀)) : by abel
            ... = res m₁'' + f.apply ((res m₁) - (d m₀)) : by
                               rw [← map_sub, ← res_apply, ← map_sub, ← sub_eq_of_eq_add' hm₁.symm],
  have hnormle : ∥mnew₁'∥ ≤ (K*K'' + 1)*∥d n∥ + (K*K'' + 2) * ε₁,
    calc ∥mnew₁'∥ = ∥res m₁'' + f.apply (res m₁ - d m₀)∥ : by rw [hmnew']
              ... ≤ ∥res m₁''∥ + ∥f.apply (res m₁ - d m₀)∥ : norm_add_le _ _
              ... ≤ ∥m₁''∥ + ∥f.apply (res m₁ - d m₀)∥ : add_le_add_right
                                               (hM'_adm.res_norm_noninc _ _ _ infer_instance m₁'') _
              ... = ∥m₁''∥ + ∥res m₁ - d m₀∥ : by rw hf
              ... ≤ ∥d n∥ + ε₁ + ∥res m₁ - d m₀∥ : add_le_add_right (le_of_lt hnorm_m₁'')  _
              ... ≤ ∥d n∥ + ε₁ + (K * K'' * ∥d n∥ + K * K'' * ε₁ + ε₁) : add_le_add_left hm₀ _
              ... = (K*K'' + 1)*∥d n∥ + (K*K'' + 2) * ε₁ : by ring,
  obtain ⟨mnew₀ : M'.X c i, hmnew₀ : ∥res mnew' - d mnew₀∥ ≤ K' * ∥d mnew'∥ + ε₁⟩ :=
    hM' _ hc _ (hi.trans (sub_one_lt m)) mnew' _ hε₁,
  replace hmnew₀ : ∥res mnew' - d mnew₀∥ ≤ K' * ((K * K'' + 1) * ∥d n∥ + (K * K'' + 2) * ε₁) + ε₁ :=
    hmnew₀.trans (add_le_add_right (mul_le_mul_of_nonneg_left hnormle nnreal.zero_le_coe) ε₁),
  let nnew₀ : ↥(N.X c i) := g.apply mnew₀,
  have hmnewlift : g.apply (res mnew' - d mnew₀) = res n - d nnew₀,
  { suffices h : g.apply mnew' = res n,
    { rw [map_sub, ← res_apply, ← d_apply, h, res_res] },
    rw map_sub,
    have hker : f.apply m₀ ∈ g.apply.ker,
    { rw [hg _ _, mem_range _ _],
      use m₀ },
    rw [(mem_ker _ _).1 hker, sub_zero, ← res_apply, hm'] },
  use nnew₀,
  rw ← hmnewlift,
  suffices : ∥res mnew' - d mnew₀∥ ≤ K' * (K * K'' + 1) * ∥d n∥ + ε,
    from (quotient_norm_le (hgquot _ _) (res mnew' - d mnew₀)).trans this,
  calc ∥res mnew' - d mnew₀∥ ≤ K' * ((K * K'' + 1) * ∥d n∥ + (K * K'' + 2) * ε₁) + ε₁ : hmnew₀
    ... = K' * (K * K'' + 1) * ∥d n∥ + (K'*(K * K'' + 2) + 1)* ε₁ : by ring
    ... = K' * (K * K'' + 1) * ∥d n∥ + ε : by rw hε₁_ε,
end
