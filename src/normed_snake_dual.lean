import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes

variables (M N P : system_of_complexes.{u}) (f : M ⟶ N) (g : N ⟶ P)

lemma weak_normed_snake_dual {k k' K K' r₁ r₂ : ℝ≥0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {a : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_weak_bounded_exact k K (a + 1) c₀)
  (hP : P.is_weak_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnorm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_weak_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
  begin
    have hfnorm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ := λ c i x, (isometry_iff_norm _).1 (hf c i) x,
    have hM_adm : M.admissible := admissible_of_isometry hN_adm hf,


    introsI c hc i hi,

    let Knew := K + r₁ * r₂ * K * K',
    have bound_nonneg : (0 : ℝ) ≤ Knew := nnreal.coe_nonneg _,
    let c₁ := k * (k' * c),
    let c₂ := k' * c,

    suffices : ∀ m : M c₁ i, ∀ ε > 0,
    ∃ i₀ (hi₀ : i₀ = i - 1) (y : M c i₀), ∥res m - M.d _ _ y∥ ≤ Knew * ∥M.d i (i + 1) m∥ + ε,
    { dsimp [c₁] at this,
      intros m₁ ε hε,
      haveI hc : fact (k * k' * c = c₁) := by { constructor, simp [mul_assoc, c₁] },
      let m : M c₁ i := res m₁,
      rcases this m ε hε with ⟨i₀, hi₀, y, hy⟩,
      rw [res_res, d_res] at hy,
      have : ∥(res (M.d i (i + 1) m₁) : M c₁ _)∥ ≤ ∥M.d _ _ m₁∥,
      { apply hM_adm.res_norm_noninc },
      refine ⟨i₀, _, hi₀, rfl, _⟩,
      exact ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left this bound_nonneg) ε)⟩ },

    intros m ε hε,

    let ε₁ := ε / 2 * (1 + K' * r₁ * r₂)⁻¹,
    have hlt : 0 < (1 + K' * r₁ * r₂ : ℝ),
    { refine add_pos_of_pos_of_nonneg zero_lt_one _,
      rw [← nnreal.coe_mul, ← nnreal.coe_mul],
      exact nnreal.coe_nonneg _ },
    have hmulε₁ : ε₁ *  (1 + K' * r₁ * r₂) = ε / 2 := by field_simp [(ne_of_lt hlt).symm],
    have hε₁ : 0 < ε₁ := mul_pos (half_pos hε) (inv_pos.2 hlt),
    let ε₂ := if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹,
    have hle : ↑r₂ * ε₂ ≤ ε / 2,
    { by_cases H : r₂ = 0,
      { simp only [H, nnreal.coe_zero, if_true, zero_mul, (half_pos hε).le], },
      { simp only [H, nnreal.coe_eq_zero, if_false, mul_ite],
        rw [mul_comm, mul_assoc, ← nnreal.coe_inv, ← nnreal.coe_mul, inv_mul_cancel H,
          nnreal.coe_one, mul_one] } },
    have hε₂ : 0 < ε₂,
    { change 0 < (if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹),
      by_cases H : r₂ = 0,
      { simp only [H, zero_lt_one, if_true, eq_self_iff_true, nnreal.coe_eq_zero] },
      { simp only [H, nnreal.coe_eq_zero, if_false],
        exact mul_pos (half_pos hε) (inv_pos.2 (nnreal.coe_pos.2 (zero_lt_iff.2 H))) } },

    let n := f m,
    obtain ⟨i', j', hi', rfl, n₁, hn₁⟩ :=
      hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (by linarith) n ε₁ hε₁,
    let p₁ := g n₁,
    have Hi' : i' ≤ a + 1 :=
      by { rw [hi', nat.sub_one], exact le_trans (nat.pred_le i) (le_trans hi (nat.le_succ a)) },
    obtain ⟨i'', j'', hi'', rfl, p₂, hp₂⟩ := hP _ hc _ Hi' p₁ ε₂ hε₂,
    have Hi'' : i'' ≤ a + 1 + 1,
    { rw [hi'', hi', nat.sub_one, nat.sub_one],
      refine le_trans (nat.pred_le _) (le_trans (nat.pred_le _) _),
      linarith },
    obtain ⟨n₂, hn₂, hnormn₂⟩ := Hg c i'' Hi'' p₂,
    let n₁' := N.d i'' i' n₂,
    obtain ⟨nnew₁, hnnew₁, hnormnnew₁⟩ := Hg c i' (le_trans Hi' (nat.le_succ _)) (g (res n₁ - n₁')),
    have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
    { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ← hom_apply, ← hom_apply, hnnew₁] },
    rw ← hg at hker,
    obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
    refine ⟨i', hi', m₁, _⟩,

    by_cases hizero : i = 0,
    { subst hizero,
      rw [nat.zero_sub] at hi',
      subst hi',
      simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
      rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
      rw ← @res_res _ c₁ c₂ c _ _ _ _,
      refine le_trans (hM_adm.res_norm_noninc _ _ _ _ _) (le_trans hn₁ _),
      rw [d_apply],
      change ↑K * ∥f.apply (M.d 0 1 m)∥ + ε₁ ≤ (K + r₁ * r₂ * K * K') * ∥M.d 0 1 m∥ + ε,
      have : (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥M.d 0 1 m∥ + ε =
        ↑K * ∥M.d 0 1 m∥ + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + ε) := by ring,
      rw [hfnorm, this],
      refine add_le_add_left ((mul_le_mul_right hlt).1 _) _,
      have hmul : (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + (ε / 2 + ε / 2)) * (1 + ↑K' * ↑r₁ * ↑r₂) =
        (ε / 2) + ((ε / 2) + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ +
        ↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ * ↑K' * ↑r₁ * ↑r₂ +
        ε * (↑K' * ↑r₁ * ↑r₂))) := by ring,
      rw [← add_halves' ε, hmulε₁, hmul, ← coe_nnnorm],
      refine (le_add_iff_nonneg_right (ε / 2)).2 (add_nonneg (half_pos hε).le _),
      exact_mod_cast add_nonneg (nnreal.coe_nonneg _) (mul_nonneg (gt.lt hε).le (nnreal.coe_nonneg _)) },

    have hii' : i' + 1 = i,
    { rw [hi', nat.sub_one, nat.add_one, nat.succ_pred_eq_of_pos (zero_lt_iff.mpr hizero)] },
    have hfm : ∥g (N.d i' i n₁)∥ = ∥g (res (f m) - N.d i' i n₁)∥,
    { have : f (@res _ c₁ (k' * c) _ _ m) ∈ f.apply.range,
      { rw mem_range,
        exact ⟨res m, rfl⟩ },
      rw [hg, mem_ker] at this,
      change ∥g ((N.d i' i) n₁)∥ = ∥g.apply (res (f m) - (N.d i' i) n₁)∥,
      rw [res_apply, normed_group_hom.map_sub, this, zero_sub, norm_neg],
      refl },

    calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
    ... = ∥f.apply (res m - (M.d i' i) m₁)∥ : rfl
    ... = ∥f.apply (res m) - f.apply (M.d i' i m₁)∥ : by rw normed_group_hom.map_sub
    ... = ∥f (res m) - f (M.d i' i m₁)∥ : rfl
    ... = ∥res n - (N.d i' i (res n₁) - N.d i' i (n₁' + nnew₁))∥ :
      by rw [← res_apply, ← d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
    ... = ∥(res n - N.d i' i (res n₁)) + N.d i' i (n₁' + nnew₁)∥ : by abel
    ... ≤ ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + ∥N.d i' i (n₁' + nnew₁) ∥ : norm_add_le _ _
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + ∥N.d i' i nnew₁∥ :
      by simp only [map_add, zero_add, d_d]
    ... ≤ ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + ∥nnew₁∥ :
      add_le_add_left (hN_adm.d_norm_noninc _ _ i' i nnew₁) _
    ... ≤ ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥g (res n₁ - n₁')∥ :
      add_le_add_left hnormnnew₁ _
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥g.apply (res n₁ - N.d i'' i' n₂)∥ : rfl
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥g.apply (res n₁) - g.apply (N.d i'' i' n₂)∥ :
      by rw normed_group_hom.map_sub
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥g (res n₁) - g (N.d i'' i' n₂)∥ : rfl
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥res (g n₁) - P.d i'' i' (g n₂)∥ :
      by rw [← res_apply, d_apply]
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥res p₁ - P.d i'' i' (g n₂)∥ : rfl
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥res p₁ - P.d i'' i' p₂∥ : by rw hn₂
    ... ≤ ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥ + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left hp₂ $ nnreal.coe_nonneg r₂) _
    ... = ∥res (@res _ c₁ c₂ _ _ n) - (@res _ c₂ c _ _ (N.d i' i n₁))∥ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥ + ε₂) :
      by rw [res_res, d_res]
    ... = ∥@res _ c₂ c _ _ (@res _ c₁ c₂ _ _ n - N.d i' i n₁)∥ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥ + ε₂) :
      by rw normed_group_hom.map_sub
    ... ≤ ∥res n - N.d i' i n₁∥ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥ + ε₂) :
      add_le_add_right (hN_adm.res_norm_noninc _ _ _ _ _) _
    ... ≤ K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥ + ε₂) :
      add_le_add_right hn₁ _
    ... = K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * ∥P.d i' (i' + 1) (g n₁)∥ + ε₂) : rfl
    ... = K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * ∥g (N.d i' i n₁)∥ + ε₂) : by rw [← d_apply, hii']
    ... = K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) : by rw hfm
    ... ≤ K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) $ nnreal.coe_nonneg K') _) $ nnreal.coe_nonneg r₂) _
    ... = K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * r₁ * ∥res n - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
    ... ≤ K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i + 1)) n∥ + ε₁) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg (nnreal.coe_nonneg K') (nnreal.coe_nonneg r₁)) _) $ nnreal.coe_nonneg r₂) _
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i + 1) n∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
    ... = Knew * ∥N.d i (i + 1) (f m)∥ + ε / 2 * (1 + K' * r₁ * r₂)⁻¹ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : rfl
    ... = Knew * ∥N.d i (i + 1) (f m)∥ + ε / 2 + r₂ * ε₂ : by rw [hmulε₁]
    ... ≤ Knew * ∥N.d i (i + 1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
    ... = Knew * ∥f (M.d i (i + 1) m)∥ + ε : by rw [add_assoc, add_halves', d_apply]
    ... = Knew * ∥f.apply (M.d i (i + 1) m)∥ + ε : rfl
    ... = Knew * ∥(M.d i (i + 1)) m∥ + ε : by rw hfnorm
  end

lemma normed_snake_dual {k k' K K' r₁ r₂ : ℝ≥0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {a : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_bounded_exact k K (a + 1) c₀)
  (hP : P.is_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnorm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
  begin
    have hfnorm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ := λ c i x, (isometry_iff_norm _).1 (hf c i) x,
    have hM_adm : M.admissible := admissible_of_isometry hN_adm hf,

    introsI c hc i hi,

    let Knew := K + r₁ * r₂ * K * K',
    have bound_nonneg : (0 : ℝ) ≤ Knew := nnreal.coe_nonneg _,
    let c₁ := k * (k' * c),
    let c₂ := k' * c,

    suffices : ∀ m : M c₁ i,
    ∃ i₀ (hi₀ : i₀ = i - 1) (y : M c i₀), ∥res m - M.d _ _ y∥ ≤ Knew * ∥M.d i (i + 1) m∥,
    { dsimp [c₁] at this,
      intros m₁,
      haveI hc : fact (k * k' * c = c₁) := by { constructor, simp [mul_assoc, c₁] },
      let m : M c₁ i := res m₁,
      rcases this m with ⟨i₀, hi₀, y, hy⟩,
      rw [res_res, d_res] at hy,
      have : ∥(res (M.d i (i + 1) m₁) : M c₁ _)∥ ≤ ∥M.d _ _ m₁∥,
      { apply hM_adm.res_norm_noninc },
      refine ⟨i₀, _, hi₀, rfl, _⟩,
      exact ⟨y, hy.trans (mul_le_mul_of_nonneg_left this bound_nonneg)⟩ },

    intro m,

    let n := f m,
    obtain ⟨i', j', hi', rfl, n₁, hn₁⟩ :=
      hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (by linarith) n,
    let p₁ := g n₁,
    have Hi' : i' ≤ a + 1 :=
      by { rw [hi', nat.sub_one], exact le_trans (nat.pred_le i) (le_trans hi (nat.le_succ a)) },
    obtain ⟨i'', j'', hi'', rfl, p₂, hp₂⟩ := hP _ hc _ Hi' p₁,
    have Hi'' : i'' ≤ a + 1 + 1,
    { rw [hi'', hi', nat.sub_one, nat.sub_one],
      refine le_trans (nat.pred_le _) (le_trans (nat.pred_le _) _),
      linarith },
    obtain ⟨n₂, hn₂, hnormn₂⟩ := Hg c i'' Hi'' p₂,
    let n₁' := N.d i'' i' n₂,
    obtain ⟨nnew₁, hnnew₁, hnormnnew₁⟩ := Hg c i' (le_trans Hi' (nat.le_succ _)) (g (res n₁ - n₁')),
    have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
    { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ← hom_apply, ← hom_apply, hnnew₁] },
    rw ← hg at hker,
    obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
    refine ⟨i', hi', m₁, _⟩,

    by_cases hizero : i = 0,
    { subst hizero,
      rw [nat.zero_sub] at hi',
      subst hi',
      simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
      rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
      rw ← @res_res _ c₁ c₂ c _ _ _ _,
      refine le_trans (hM_adm.res_norm_noninc _ _ _ _ _) (le_trans hn₁ _),
      rw [d_apply],
      change ↑K * ∥f.apply (M.d 0 1 m)∥ ≤ (K + r₁ * r₂ * K * K') * ∥M.d 0 1 m∥,
      have : (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥M.d 0 1 m∥ =
        ↑K * ∥M.d 0 1 m∥ + ↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ := by ring,
      rw [hfnorm, this],
      refine le_add_of_nonneg_right (_),
      rw [← nnreal.coe_mul, ← nnreal.coe_mul, ← nnreal.coe_mul],
      exact mul_nonneg (nnreal.coe_nonneg _) (norm_nonneg _) },

    have hii' : i' + 1 = i,
    { rw [hi', nat.sub_one, nat.add_one, nat.succ_pred_eq_of_pos (zero_lt_iff.mpr hizero)] },
    have hfm : ∥g (N.d i' i n₁)∥ = ∥g (res (f m) - N.d i' i n₁)∥,
    { have : f (@res _ c₁ (k' * c) _ _ m) ∈ f.apply.range,
      { rw mem_range,
        exact ⟨res m, rfl⟩ },
      rw [hg, mem_ker] at this,
      change ∥g ((N.d i' i) n₁)∥ = ∥g.apply (res (f m) - (N.d i' i) n₁)∥,
      rw [res_apply, normed_group_hom.map_sub, this, zero_sub, norm_neg],
      refl },

    calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
    ... = ∥f.apply (res m - (M.d i' i) m₁)∥ : rfl
    ... = ∥f.apply (res m) - f.apply (M.d i' i m₁)∥ : by rw normed_group_hom.map_sub
    ... = ∥f (res m) - f (M.d i' i m₁)∥ : rfl
    ... = ∥res n - (N.d i' i (res n₁) - N.d i' i (n₁' + nnew₁))∥ :
      by rw [← res_apply, ← d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
    ... = ∥(res n - N.d i' i (res n₁)) + N.d i' i (n₁' + nnew₁)∥ : by abel
    ... ≤ ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + ∥N.d i' i (n₁' + nnew₁) ∥ : norm_add_le _ _
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + ∥N.d i' i nnew₁∥ :
      by simp only [map_add, zero_add, d_d]
    ... ≤ ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + ∥nnew₁∥ :
      add_le_add_left (hN_adm.d_norm_noninc _ _ i' i nnew₁) _
    ... ≤ ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥g (res n₁ - n₁')∥ :
      add_le_add_left hnormnnew₁ _
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥g.apply (res n₁ - N.d i'' i' n₂)∥ : rfl
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥g.apply (res n₁) - g.apply (N.d i'' i' n₂)∥ :
      by rw normed_group_hom.map_sub
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥g (res n₁) - g (N.d i'' i' n₂)∥ : rfl
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥res (g n₁) - P.d i'' i' (g n₂)∥ :
      by rw [← res_apply, d_apply]
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥res p₁ - P.d i'' i' (g n₂)∥ : rfl
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥res p₁ - P.d i'' i' p₂∥ : by rw hn₂
    ... ≤ ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥) :
      add_le_add_left (mul_le_mul_of_nonneg_left hp₂ $ nnreal.coe_nonneg r₂) _
    ... = ∥res (@res _ c₁ c₂ _ _ n) - (@res _ c₂ c _ _ (N.d i' i n₁))∥ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥) :
      by rw [res_res, d_res]
    ... = ∥@res _ c₂ c _ _ (@res _ c₁ c₂ _ _ n - N.d i' i n₁)∥ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥) :
      by rw normed_group_hom.map_sub
    ... ≤ ∥res n - N.d i' i n₁∥ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥) :
      add_le_add_right (hN_adm.res_norm_noninc _ _ _ _ _) _
    ... ≤ K * ∥N.d i (i + 1) n∥ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥) :
      add_le_add_right hn₁ _
    ... = K * ∥N.d i (i + 1) n∥ + r₂ * (K' * ∥P.d i' (i' + 1) (g n₁)∥) : rfl
    ... = K * ∥N.d i (i + 1) n∥ + r₂ * (K' * ∥g (N.d i' i n₁)∥) : by rw [← d_apply, hii']
    ... = K * ∥N.d i (i + 1) n∥ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥) : by rw hfm
    ... ≤ K * ∥N.d i (i + 1) n∥ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥)) :
      add_le_add_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) $ nnreal.coe_nonneg K') $ nnreal.coe_nonneg r₂) _
    ... = K * ∥N.d i (i + 1) n∥ + r₂ * (K' * r₁ * ∥res n - N.d i' i n₁∥) : by rw mul_assoc
    ... ≤ K * ∥N.d i (i + 1) n∥ + r₂ * (K' * r₁ * (K * ∥(N.d i (i + 1)) n∥)) :
      add_le_add_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg (nnreal.coe_nonneg K') (nnreal.coe_nonneg r₁)) $ nnreal.coe_nonneg r₂) _
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i + 1) n∥ : by ring
    ... = Knew * ∥N.d i (i + 1) (f m)∥ : rfl
    ... = Knew * ∥f (M.d i (i + 1) m)∥ : by rw d_apply
    ... = Knew * ∥f.apply (M.d i (i + 1) m)∥ : rfl
    ... = Knew * ∥(M.d i (i + 1)) m∥ : by rw hfnorm
  end
