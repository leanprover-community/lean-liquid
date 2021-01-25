import system_of_complexes

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom

section prereqs -- move this
variables {V W : Type*} [normed_group V] [normed_group W]

def normed_group_hom.is_strict (f : normed_group_hom V W) : Prop :=
∀ v, ∥f v∥ = ∥v∥

lemma normed_group_hom.is_strict.injective {f : normed_group_hom V W} (hf : f.is_strict) :
  function.injective f :=
begin
  intros x y h,
  rw ← sub_eq_zero at *,
  suffices : ∥ x - y ∥ = 0, by simpa,
  rw ← hf,
  simpa,
end

end prereqs

variables {M M' N : system_of_complexes.{u}} (f : M ⟶ M') (g : M' ⟶ N)

def category_theory.has_hom.hom.apply (f : M ⟶ N) (c : ℝ≥0) (i : ℤ) :=
(f.app (op c)).f i

variables (M M' N)

lemma commutes (f : M ⟶ N) {c : ℝ≥0} {i : ℤ} (m : M.X c i) :
  N.d (f.apply c i m) = f.apply c (i + 1) (M.d m) :=
begin
  have h : ((M.obj (op c)).d i ≫ (f.app (op c)).f (i + 1)) m =
    (f.app (op c)).f (i + 1) ((M.obj (op c)).d i m),
  { exact coe_comp ((M.obj (op c)).d i) ((f.app (op c)).f (i + 1)) m },
  rwa [homological_complex.comm_at (f.app (op c)) i] at h,
end

lemma commutes_res (f : M ⟶ N) (c c' : ℝ≥0) [h : fact (c ≤ c')] {i : ℤ} (m : M.X c' i) :
  @system_of_complexes.res N c' c _ _ (f.apply c' i m) =
  f.apply c i (@system_of_complexes.res M c' c _ _ m) :=
begin
  sorry
end

lemma quotient_norm {M N : NormedGroup} {f : M ⟶ N} (hsur : function.surjective f)
  (hquot : ∀ x, ∥f x∥ = Inf {r : ℝ | ∃ y ∈ f.ker, r = ∥x + y∥ }) {ε : ℝ} (hε : 0 < ε)
  (n : N) : ∃ (m : M), f m = n ∧ ∥m∥ < ∥n∥ + ε :=
begin
  have hlt := lt_add_of_pos_right (∥n∥) hε,
  obtain ⟨m, hm⟩ := hsur n,
  nth_rewrite 0 [← hm] at hlt,
  rw [hquot m] at hlt,
  replace hlt := (real.Inf_lt _ _ _).1 hlt,
  { obtain ⟨r, hr, hlt⟩ := hlt,
    simp only [exists_prop, set.mem_set_of_eq] at hr,
    obtain ⟨m₁, hm₁⟩ := hr,
    use (m + m₁),
    split,
    { rw [map_add, (mem_ker f m₁).1 hm₁.1, add_zero, hm] },
    rwa [← hm₁.2] },
  { use ∥m∥,
    simp only [exists_prop, set.mem_set_of_eq],
    use 0,
    split,
    { exact (ker f).zero_mem },
    { rw add_zero } },
  { use 0,
    intros x hx,
    simp only [exists_prop, set.mem_set_of_eq] at hx,
    obtain ⟨y, hy⟩ := hx,
    rw hy.2,
    exact norm_nonneg _ }
end

lemma quotient_norm_le {M N : NormedGroup} {f : M ⟶ N} (hsur : function.surjective f)
  (hquot : ∀ x, ∥f x∥ = Inf {r : ℝ | ∃ y ∈ f.ker, r = ∥x + y∥ }) (m : M) : ∥f m∥ ≤ ∥m∥ :=
begin
  rw hquot,
  apply real.Inf_le,
  { use 0,
    rintros y ⟨r,hr,rfl⟩,
    simp },
  { refine ⟨0, add_subgroup.zero_mem _, by simp⟩ }
end

/-- The normed snake lemma. See Proposition 9.10 from Analytic.pdf -/
lemma weak_normed_snake (k : ℝ≥0) (m : ℤ) (c₀ : ℝ≥0) [hk : fact (1 ≤ k)]
  (hf : ∀ c i, normed_group_hom.is_strict (f.apply c i))
  (Hf : ∀ (c : ℝ≥0) (i : ℤ) (hi : i ≤ m + 1) (x : M.X (k * c) i),
    ∥(M.res x : M.X c i)∥ ≤ k * ∥f.apply (k * c) i x∥)
  (hg : ∀ c i, (g.apply c i).ker = (f.apply c i).range)
  (hgsur : ∀ c i, function.surjective (g.apply c i))
  (hN : ∀ c i x, ∥g.apply c i x∥ = Inf {r : ℝ | ∃ y ∈ (g.apply c i).ker, r = ∥x + y∥ })
  (hM : M.is_weak_bdd_exact_for_bdd_degree_above_idx k m c₀)
  (hM' : M'.is_weak_bdd_exact_for_bdd_degree_above_idx k m c₀)
  (hM_adm : M.admissible)
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
  set n := @system_of_complexes.res _ _ c_new _ _ norig with hn,
  haveI : fact (c ≤ c_new) :=
  calc c ≤ k * c             : le_mul_of_one_le_left' hk
     ... ≤ k * (k * c)       : le_mul_of_one_le_left' hk
     ... ≤ k * (k * (k * c)) : le_mul_of_one_le_left' hk,
  have honele : 1 ≤ k^3 + 2 * k + 1, by {change fact _, apply_instance},
  have hzerok : ↑k ^ 3 + 2 * ↑k + 1 ≠ (0 : ℝ),
  { refine ne_of_gt (lt_of_lt_of_le zero_lt_one _),
    exact_mod_cast honele },
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
    simp only [system_of_complexes.res_res] at ha,
    calc _ ≤ _ : ha
       ... ≤ _ : _,
    simp only [hn, nnreal.coe_add, add_le_add_iff_right, nnreal.coe_pow],
    apply mul_le_mul_of_nonneg_left,
    { rw system_of_complexes.d_res,
      have hN_adm : N.admissible,
      { sorry },
      convert hN_adm.res_norm_noninc _ _ _ _ (N.d norig),
      simp only [one_mul, nnreal.coe_one], },
    { exact_mod_cast (nnreal.coe_nonneg (k ^ 3 + k)) } },

  obtain ⟨m', hm'⟩ := hgsur _ _ n,
  let m₁' := M'.d m',
  have hm₁' : g.apply _ _ m₁' = N.d n := by simpa [hm'] using (commutes _ _ g m').symm,
  obtain ⟨m₁'', hm₁''⟩ := quotient_norm (hgsur _ _) (hN _ _) hε₁ (N.d n),
  have hm₁exist : ∃ m₁ : M.X _ _,  f.apply _ _ m₁ + m₁'' = m₁',
  { have hrange : m₁' - m₁'' ∈ (f.apply _ _).range,
    { rw [← hg _ _, mem_ker  _ _, map_sub, hm₁', hm₁''.1, sub_self] },
    obtain ⟨m₁, hm₁⟩ := (mem_range _ _).1 hrange,
    exact ⟨m₁, by rw [hm₁, sub_add_cancel]⟩ },
  obtain ⟨m₁, hm₁⟩ := hm₁exist,
  have hm₂ : f.apply _ _ (M.d m₁) = -(M'.d m₁''),
  { rw [← commutes, eq_sub_of_add_eq hm₁, map_sub, ← coe_comp, system_of_complexes.d,
      system_of_complexes.d, homological_complex.d_squared, coe_zero, ← neg_inj, pi.zero_apply,
      zero_sub], },
  have hle := Hf _ _ hi3 (M.d m₁),
  rw [hm₂, norm_neg] at hle,
  replace hle := le_trans hle (mul_le_mul_of_nonneg_left (hM'_adm.d_norm_noninc _ _ m₁'')
    (le_trans zero_le_one hk)),
  rw [nnreal.coe_one, one_mul] at hle,
  replace hle := le_trans hle (mul_le_mul_of_nonneg_left (le_of_lt hm₁''.2)
    (le_trans zero_le_one hk)),
  obtain ⟨m₀, hm₀⟩ := hM _ hkc _ hi1 (M.res m₁) ε₁ hε₁,
  rw [system_of_complexes.res_res, system_of_complexes.d_res _] at hm₀,
  let mnew' := (M'.res m')  - (f.apply _ _ m₀),
  let mnew₁' := M'.d mnew',
  have hmnew' : mnew₁' = M'.res m₁'' + f.apply _ _ (M.res m₁ - M.d m₀),
  { calc mnew₁' = M'.d ((M'.res m')  - (f.apply _ _ m₀)) : by refl
            ... = M'.res (M'.d m')  - (f.apply _ _ (M.d m₀)) : by rw [map_sub,
              system_of_complexes.d_res _, commutes _]
            ... = M'.res (M'.d m')  - (f.apply _ _ (M.res m₁)) +
              ((f.apply _ _ (M.res m₁)) - (f.apply _ _ (M.d m₀))) : by abel
            ... = M'.res m₁'' + f.apply _ _ ((M.res m₁) - (M.d m₀)) : by
              rw [← map_sub, ← commutes_res _ _ _, ← map_sub, ← sub_eq_of_eq_add' hm₁.symm] },
  have hnormle : ∥mnew₁'∥ ≤ (∥N.d n∥ + ε₁) * (k ^ 2  + 1) + ε₁,
  { replace hm₀ := le_trans hm₀ (add_le_add_right (mul_le_mul_of_nonneg_left hle
      (@nnreal.zero_le_coe k)) ε₁),
    rw [← mul_assoc ↑k _ _] at hm₀,
    calc ∥mnew₁'∥ = ∥M'.res m₁'' + f.apply _ _ (M.res m₁ - M.d m₀)∥ : by rw [hmnew']
              ... ≤ ∥M'.res m₁''∥ + ∥f.apply _ _ (M.res m₁ - M.d m₀)∥ : norm_add_le _ _
              ... ≤ 1 * ∥m₁''∥ + ∥f.apply _ _ (M.res m₁ - M.d m₀)∥ : add_le_add_right
                (hM'_adm.res_norm_noninc _ _ _ kccnew m₁'') _
              ... = ∥m₁''∥ + ∥M.res m₁ - M.d m₀∥ : by rw [hf _ _ _, one_mul]
              ... ≤ ∥N.d n∥ + ε₁ + ∥M.res m₁ - M.d m₀∥ : add_le_add_right (le_of_lt hm₁''.2)  _
              ... ≤ ∥N.d n∥ + ε₁ + (k * k * (∥N.d n∥ + ε₁) + ε₁) : add_le_add_left hm₀ _
              ... = (∥N.d n∥ + ε₁) * (k ^ 2  + 1) + ε₁ : by ring },
  obtain ⟨mnew₀, hmnew₀⟩ := hM' _ hc _ (lt_trans hi (sub_one_lt m)) mnew' _ hε₁,
  replace hmnew₀ := le_trans hmnew₀ (add_le_add_right (mul_le_mul_of_nonneg_left
    hnormle (@nnreal.zero_le_coe k)) ε₁),
  let nnew₀ := g.apply _ _ mnew₀,
  have hmnewlift : g.apply _ _ ((M'.res mnew') - (M'.d mnew₀)) = N.res n - N.d nnew₀,
  { suffices h : g.apply _ _ mnew' = N.res n,
    { rw [map_sub, ← commutes_res, ← commutes, h, system_of_complexes.res_res] },
    rw [map_sub],
    have hker : (f.apply _ _) m₀ ∈ (g.apply _ _).ker,
    { rw [hg _ _, mem_range _ _],
      use m₀ },
    rw [(mem_ker _ _).1 hker, sub_zero, ← commutes_res, hm'] },
  use nnew₀,
  rw [← hmnewlift],
  suffices : ∥M'.res mnew' - (M'.d) mnew₀∥ ≤ (k ^ 3 + k) * ∥N.d n∥ + ε,
  { exact le_trans (quotient_norm_le (hgsur _ _) (hN _ _) (M'.res mnew' - (M'.d) mnew₀)) this },
  calc ∥(M'.res) mnew' - (M'.d) mnew₀∥ ≤ k * ((∥N.d n∥ + ε₁) * (k ^ 2 + 1) + ε₁) + ε₁ : hmnew₀
    ... = (k ^ 3 + k) * ∥N.d n∥ + (k ^ 3 + 2 * k + 1) * ε₁ : by ring
    ... = (k ^ 3 + k) * ∥N.d n∥ + (k ^ 3 + 2 * k + 1) * (ε / (↑k ^ 3 + 2 * ↑k + 1)) : by refl
    ... = (k ^ 3 + k) * ∥N.d n∥ + (k ^ 3 + 2 * k + 1) * ε / (k ^ 3 + 2 * k + 1) : by ring
    ... = (k ^ 3 + k) * ∥N.d n∥ + ε : by rw mul_div_cancel_left ε hzerok
end
