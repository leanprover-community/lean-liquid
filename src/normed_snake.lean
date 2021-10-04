import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes

variables (M M' N : system_of_complexes.{u}) (f : M ⟶ M') (g : M' ⟶ N)

/-- The normed snake lemma, weak version. See Proposition 9.10 from Analytic.pdf -/
--TODO Add the non weak version for complete system of complexes
lemma weak_normed_snake {k k' k'' K K' K'' : ℝ≥0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')] [hk'' : fact (1 ≤ k'')]
  {m : ℕ} {c₀ : ℝ≥0}
  (hM : M.is_weak_bounded_exact k K (m+1) c₀)
  (hM' : M'.is_weak_bounded_exact k' K' (m+1) c₀)
  (hM'_adm : M'.admissible)
  (hf : ∀ c i, (f.apply : M c i ⟶ M' c i).norm_noninc)
  (Hf : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ m+1+1) (x : M (k'' * c) i),
    ∥(res x : M c i)∥ ≤ K'' * ∥f x∥)
  (hg : ∀ c i, (g.apply : M' c i ⟶ N c i).ker = f.apply.range)
  (hgquot : system_of_complexes.is_quotient g) :
  N.is_weak_bounded_exact (k''*k*k') (K'*(K*K'' + 1)) m c₀ :=
begin
  introsI c hc i hi,
  let c₁ := k'' * (k * (k' * c)),
  suffices : ∀ n : N c₁ i, ∀ ε > 0,
    ∃ i₀ (hi₀ : i₀ = i - 1) (y : N c i₀),
      ∥res n - N.d _ _ y∥ ≤ K' * (K * K'' + 1) * ∥N.d i (i+1) n∥ + ε,
  { dsimp [c₁] at this,
    intros n₁ ε hε,
    haveI hc : fact (k'' * k * k' * c = c₁) :=
      { out := (mul_assoc _ _ _).trans ((mul_assoc _ _ _).trans rfl) },
    rcases this (res n₁) ε hε with ⟨i₀, hi₀, y, hy⟩,
    rw [res_res, d_res] at hy,
    refine ⟨i₀, _, hi₀, rfl, _⟩,
    refine ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left _ _) ε)⟩,
    { apply (admissible_of_quotient hgquot hM'_adm).res_norm_noninc },
    { exact (nnreal.zero_le_coe : 0 ≤ K' * (K * K'' + 1)) } },
  intros n ε hε,
  let ε₁ := ε/(K' * (K * K'' + 2) + 1),

  have hε₁ : 0 < ε₁ :=
    div_pos hε (lt_of_lt_of_le zero_lt_one (nnreal.one_le_add'.out : 1 ≤ K' * (K * K'' + 2) + 1)),

  obtain ⟨m' : M' c₁ i, rfl : g m' = n⟩ := (hgquot _ _).surjective _,
  let m₁' := M'.d i (i+1) m',
  have hm₁' : g m₁' = N.d i (i+1) (g m') := (d_apply _ _ g m').symm,
  obtain ⟨m₁'' : M' c₁ (i+1),
          hgm₁'' : g m₁'' = N.d i (i+1) (g m'),
          hnorm_m₁'' : ∥m₁''∥ < ∥N.d i (i+1) (g m')∥ + ε₁⟩ :=
    (hgquot _ _).norm_lift hε₁ (N.d i (i+1) (g m')),
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : M c₁ (i+1), f m₁ + m₁'' = m₁',
  { have hrange : m₁' - m₁'' ∈ f.apply.range,
    { rw [← hg _ _, mem_ker  _ _, normed_group_hom.map_sub],
      change g m₁' - g m₁'' = 0,
      rw [hm₁', hgm₁'', sub_self] },
    obtain ⟨m₁, hm₁ : f m₁ = m₁' - m₁''⟩ := (mem_range _ _).1 hrange,
    exact ⟨m₁, by rw [hm₁, sub_add_cancel]⟩ },

  have him : i+2 ≤ m+2 := add_le_add_right hi _,
  have hm₂ : f (M.d (i+1) (i+2) m₁) = -M'.d (i+1) (i+2) m₁'',
  { rw [← d_apply, eq_sub_of_add_eq hm₁, normed_group_hom.map_sub, ← category_theory.comp_apply,
       d_comp_d, coe_zero, ← neg_inj, pi.zero_apply, zero_sub], },
  have hle : ∥res (M.d (i+1) (i+2) m₁)∥ ≤ K'' * ∥m₁''∥,
  { calc ∥res (M.d (i+1) (i+2) m₁)∥
        ≤ K'' * ∥f (M.d (i+1) (i+2) m₁)∥ : Hf _ _ him _
    ... = K'' * ∥M'.d (i+1) (i+2) m₁''∥ : by rw [hm₂, norm_neg]
    ... ≤ K'' * ∥m₁''∥ : (mul_le_mul_of_nonneg_left
                           (hM'_adm.d_norm_noninc _ _ _ _ m₁'') $ nnreal.coe_nonneg K'') },
  obtain ⟨i', j, hi', rfl, m₀, hm₀⟩ :=
    hM _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (nat.succ_le_succ hi) (res m₁) ε₁ hε₁,
  rw [← nat.pred_eq_sub_one, i.pred_succ] at hi', subst i',
  replace hm₀ : ∥res m₁ - M.d i (i+1) m₀∥ ≤ K * K'' * ∥N.d i (i+1) (g m')∥ + K*K''*ε₁ + ε₁,
  { calc ∥res m₁ - M.d i (i+1) m₀∥  = ∥res (res m₁) - M.d i (i+1) m₀∥ : by rw res_res
    ... ≤ K * ∥M.d (i+1) (i+2) (res m₁)∥ + ε₁ : hm₀
    ... = K * ∥res (M.d (i+1) (i+2) m₁)∥ + ε₁ : by rw d_res
    ... ≤ K*(K'' * ∥m₁''∥) + ε₁ : add_le_add_right (mul_le_mul_of_nonneg_left hle nnreal.zero_le_coe) _
    ... ≤ K*(K'' * (∥N.d i (i+1) (g m')∥ + ε₁)) + ε₁ :  add_le_add_right (mul_le_mul_of_nonneg_left
                                        (mul_le_mul_of_nonneg_left hnorm_m₁''.le nnreal.zero_le_coe)
                                         nnreal.zero_le_coe) ε₁
    ... = K * K'' * ∥N.d i (i+1) (g m')∥ + K*K''*ε₁ + ε₁ : by ring },

  let mnew₁' := M'.d i (i+1) (res m' - f m₀),
  have hmnew' : mnew₁' = res m₁'' + f (res m₁ - M.d i (i+1) m₀),
  { calc mnew₁'
        = M'.d i (i+1) (res m' - f m₀) : rfl
    ... = res (M'.d i (i+1) m') - (f (M.d i (i+1) m₀)) : by rw [normed_group_hom.map_sub, d_res _, d_apply]
    ... = res (M'.d i (i+1) m') - (f (res m₁)) + (f (res m₁) - f (M.d i (i+1) m₀)) : by abel
    ... = res m₁'' + f ((res m₁) - (M.d i (i+1) m₀)) : by
                        { rw [← system_of_complexes.map_sub, ← res_apply,
                              ← normed_group_hom.map_sub, ← sub_eq_of_eq_add' hm₁.symm] } },
  have hnormle : ∥mnew₁'∥ ≤ (K*K'' + 1)*∥N.d i (i+1) (g m')∥ + (K*K'' + 2) * ε₁,
  { calc ∥mnew₁'∥
        = ∥res m₁'' + f (res m₁ - M.d i (i+1) m₀)∥ : by rw [hmnew']
    ... ≤ ∥res m₁''∥ + ∥f (res m₁ - M.d i (i+1) m₀)∥ : norm_add_le _ _
    ... ≤ ∥m₁''∥ + ∥f (res m₁ - M.d i (i+1) m₀)∥ : add_le_add_right
                                      (hM'_adm.res_norm_noninc _ _ _ _ m₁'') _
    ... ≤ ∥m₁''∥ + ∥res m₁ - M.d i (i+1) m₀∥ : add_le_add_left (hf _ _ _) _
    ... ≤ ∥N.d i (i+1) (g m')∥ + ε₁ + ∥res m₁ - M.d i (i+1) m₀∥ : add_le_add_right (le_of_lt hnorm_m₁'')  _
    ... ≤ ∥N.d i (i+1) (g m')∥ + ε₁ + (K * K'' * ∥N.d i (i+1) (g m')∥ + K * K'' * ε₁ + ε₁) : add_le_add_left hm₀ _
    ... = (K*K'' + 1)*∥d _ _ (i+1) (g m')∥ + (K*K'' + 2) * ε₁ : by ring },
  obtain ⟨i₀, _, hi₀, rfl, mnew₀, hmnew₀⟩ := hM' _ hc _ (hi.trans m.le_succ) (res m' - f m₀) _ hε₁,
  replace hmnew₀ : ∥res (res m' - f m₀) - d _ _ _ mnew₀∥ ≤
    K' * ((K * K'' + 1) * ∥N.d i (i+1) (g m')∥ + (K * K'' + 2) * ε₁) + ε₁ :=
    hmnew₀.trans (add_le_add_right (mul_le_mul_of_nonneg_left hnormle nnreal.zero_le_coe) ε₁),
  let nnew₀ : ↥(N c i₀) := g mnew₀,
  have hmnewlift : g (res (res m' - f m₀) - M'.d i₀ i mnew₀) = res (g m') - N.d i₀ i nnew₀,
  { suffices h : g (res m' - f m₀) = res (g m'),
    { rw [system_of_complexes.map_sub, ← res_apply, ← d_apply, h, res_res] },
    rw system_of_complexes.map_sub,
    have hker : f m₀ ∈ g.apply.ker,
    { rw [hg _ _, mem_range _ _],
      exact ⟨m₀, rfl⟩ },
    replace hker : g (f m₀) = 0, { rwa mem_ker at hker },
    rw [hker, sub_zero, ← res_apply] },
  refine ⟨i₀, hi₀, nnew₀, _⟩,
  rw ← hmnewlift,
  refine ((hgquot _ _).norm_le _).trans (hmnew₀.trans (le_of_eq _)),
  have hε₁_ε : (K' * (K * K'' + 2) + 1 : ℝ)*ε₁ = ε := mul_div_cancel' _
    (by { refine (lt_of_lt_of_le zero_lt_one _).ne',
          exact (nnreal.one_le_add'.out : 1 ≤ K' * (K * K'' + 2) + 1) }),
  rw ← hε₁_ε,
  ring,
end
