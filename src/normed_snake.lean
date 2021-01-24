import system_of_complexes

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite

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
    { rw [normed_group_hom.map_add, (normed_group_hom.mem_ker f m₁).1 hm₁.1, add_zero, hm] },
    rwa [← hm₁.2] },
  { use ∥m∥,
    simp only [exists_prop, set.mem_set_of_eq],
    use 0,
    split,
    { exact (normed_group_hom.ker f).zero_mem },
    { rw add_zero } },
  { use 0,
    intros x hx,
    simp only [exists_prop, set.mem_set_of_eq] at hx,
    obtain ⟨y, hy⟩ := hx,
    rw hy.2,
    exact norm_nonneg _ }
end

/-- The normed snake lemma. See Proposition 9.10 from Analytic.pdf -/
lemma normed_snake (k : ℝ≥0) (m : ℤ) (c₀ : ℝ≥0) [hk : fact (1 ≤ k)]
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
  haveI : fact (c_new ≤ (k ^ 3 + k) * c) := by
  { show k * (k * (k * c)) ≤ (k ^ 3 + k) * c,
    rw add_mul,
    convert (le_add_iff_nonneg_right (k^3 * c)).2 (zero_le') using 1,
    ring },
  set n := @system_of_complexes.res _ _ c_new _ _ norig with hn,
  set n₁ := N.d n with hn₁,
  let C := ∥n₁∥,
  haveI : fact (c ≤ c_new) :=
  calc c ≤ k * c             : le_mul_of_one_le_left' hk
     ... ≤ k * (k * c)       : le_mul_of_one_le_left' hk
     ... ≤ k * (k * (k * c)) : le_mul_of_one_le_left' hk,
  suffices hnorig : ∃ (y : (N.X c i)), ∥(N.res) n - (N.d) y∥ ≤ (k ^ 3 + k) * C + ε,
  { refine Exists.imp _ hnorig,
    rintro a ha,
    simp only [system_of_complexes.res_res] at ha,
    calc _ ≤ _ : ha
       ... ≤ _ : _,
    simp only [C, hn₁, hn, nnreal.coe_add, add_le_add_iff_right, nnreal.coe_pow],
    apply mul_le_mul_of_nonneg_left,
    { rw system_of_complexes.d_res,
      have hN_adm : N.admissible :=
      begin
        sorry,
      end,
      convert hN_adm.res_norm_noninc _ _ _ _ (N.d norig),
      simp, },
    { exact_mod_cast (nnreal.coe_nonneg (k^3 + k)), }, },
  obtain ⟨m', hm'⟩ := hgsur _ _ n,
  let m₁' := M'.d m',
  have hm₁' : g.apply _ _ m₁' = n₁,
  { rw [hn₁, ← hm'],
    exact (commutes M' N g m').symm },
  --I have to check, but probably we need to use something like ε₁ = ε/(k^3+k) in the following
  obtain ⟨m₁'', hm₁''⟩ := quotient_norm (hgsur _ _) (hN _ _) hε n₁,
  have hm₁exist : ∃ m₁ : M.X _ _, m₁' = f.apply _ _ m₁ + m₁'',
  { have hrange : m₁' - m₁'' ∈ (f.apply _ _).range,
    { rw [← hg _ _, normed_group_hom.mem_ker  _ _, normed_group_hom.map_sub, hm₁',
        hm₁''.1, sub_self] },
    obtain ⟨m₁, hm₁⟩ := (normed_group_hom.mem_range _ _).1 hrange,
    use m₁,
    rw [hm₁, sub_add_cancel] },
  obtain ⟨m₁, hm₁⟩ := hm₁exist,
  let m₂ := M.d m₁,
  let m₂'' := M'.d m₁'',
  have hm₂ : f.apply _ _ m₂ = -m₂'',
  { rw [← commutes _ _ _, eq_sub_of_add_eq hm₁.symm, normed_group_hom.map_sub, ← coe_comp _ _ _,
      system_of_complexes.d, system_of_complexes.d, homological_complex.d_squared _ _,
      normed_group_hom.coe_zero, ← neg_inj, pi.zero_apply, zero_sub, neg_neg, neg_neg,
      ← system_of_complexes.d] },
  have hi3 : i + 1 + 1 + 1 ≤ m + 1 := by linarith,
  have hle := Hf _ _ hi3 m₂,
  rw [hm₂, norm_neg] at hle,
  replace hle := le_trans hle (mul_le_mul_of_nonneg_left (hM'_adm.d_norm_noninc _ _ m₁'')
    (le_trans zero_le_one hk)),
  rw [nnreal.coe_one, one_mul] at hle,
  replace hle := le_trans hle (mul_le_mul_of_nonneg_left (le_of_lt hm₁''.2)
    (le_trans zero_le_one hk)),
  have hkc : c₀ ≤ k * c := le_trans hc (le_mul_of_one_le_left' hk),
  have hi1 : i + 1 < m := by linarith,
  obtain ⟨m, hm⟩ := hM (k * c) hkc _ hi1 (M.res m₁) ε hε,
  rw [system_of_complexes.res_res, system_of_complexes.d_res _] at hm,
  letI : fact (k * c ≤ c_new) := sorry,
  let mnew' := (M'.res m')  - (f.apply _ _ m),
  have hmnewlift : g.apply _ _ mnew' = N.res n,
  {
    sorry --easy. Maybe better to postpone to the end?
  },
  let mnew₁' := M'.d mnew',
  have hmnew' : mnew₁' = M'.res m₁'' + f.apply _ _ (M.res m₁ - M.d m),
  { calc mnew₁' = M'.d ((M'.res m')  - (f.apply _ _ m)) : by refl
            ... = M'.res (M'.d m')  - (f.apply _ _ (M.d m)) : by rw [normed_group_hom.map_sub,
              system_of_complexes.d_res _, commutes _]
            ... = M'.res (M'.d m')  - (f.apply _ _ (M.res m₁)) +
              ((f.apply _ _ (M.res m₁)) - (f.apply _ _ (M.d m))) : by abel
            ... = M'.res m₁'' + f.apply _ _ ((M.res m₁) - (M.d m)) : by
              rw [← normed_group_hom.map_sub, ← commutes_res _ _ _, ← normed_group_hom.map_sub,
              ← sub_eq_of_eq_add' hm₁] },
  sorry,

end
