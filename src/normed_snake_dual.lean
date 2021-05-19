import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes

structure add_subgroup.is_kernel {M N : Type*} [semi_normed_group M] [semi_normed_group N]
  (f : normed_group_hom M N) : Prop :=
(injective : function.injective f)
(norm : ∀ x, ∥f x∥ = ∥x∥)

def system_of_complexes.is_kernel {M M' : system_of_complexes} (f : M ⟶ M') : Prop :=
∀ c i, add_subgroup.is_kernel (f.apply : M c i ⟶ M' c i)

lemma admissible_of_kernel {M M' : system_of_complexes} {f : M ⟶ M'}
  (hker : system_of_complexes.is_kernel f) (hadm : M'.admissible) : M.admissible :=
begin
  sorry
end

variables (M N P : system_of_complexes.{u}) (f : M ⟶ N) (g : N ⟶ P)

lemma weak_normed_snake_dual {k k' K K' r₁ r₂ : ℝ≥0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {m : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_weak_bounded_exact k K (m+1) c₀)
  (hP : P.is_weak_bounded_exact k' K' (m+1) c₀)
  (hN_adm : N.admissible)
  (hgnorm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ m+1+1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hfker : system_of_complexes.is_kernel f) :
  M.is_weak_bounded_exact (k * k') (K + r₁ * r₂ * K * K') m c₀ :=
  begin
    let Knew := K + r₁ * r₂ * K * K',
    have bound_nonneg : (0 : ℝ) ≤ Knew := sorry,
    introsI c hc i hi,
    let c₁ := k * (k' * c),
    let c₂ := k' * c,
    suffices : ∀ m : M c₁ i, ∀ ε > 0,
    ∃ i₀ (hi₀ : i₀ = i - 1) (y : M c i₀), ∥res m - M.d _ _ y∥ ≤ Knew * ∥M.d i (i+1) m∥ + ε,
    { dsimp [c₁] at this,
      intros m₁ ε hε,
      haveI hc : fact (k * k' * c = c₁) := by { constructor, simp [mul_assoc, c₁] },
      let m : ↥(M c₁ i) := res m₁,
      rcases this m ε hε with ⟨i₀, hi₀, y, hy⟩,
      rw [res_res, d_res] at hy,
      have : ∥(res (M.d i (i+1) m₁) : M (k * (k' * c)) (i+1))∥ ≤ ∥M.d i (i+1) m₁∥,
      { apply (admissible_of_kernel hfker hN_adm).res_norm_noninc },
      refine ⟨i₀, _, hi₀, rfl, _⟩,
      refine ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left this bound_nonneg) ε)⟩ },

    intros m ε hε,
    let ε₁ := (ε / 2) * (1 + K' * r₁ * r₂)⁻¹,
    have hneq : (1 + K' * r₁ * r₂ : ℝ) ≠ 0 := sorry,
    have hε₁ : 0 < ε₁ := sorry,
    let ε₂ := if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹,
    have hle : ↑r₂ * ε₂ ≤ ε / 2,
    { by_cases H : (r₂ : ℝ) = 0,
      { simp only [H, (half_pos hε).le, if_true, zero_mul] },
      { simp only [H, if_false, mul_ite],
        rw [mul_comm, mul_assoc, inv_mul_cancel H, mul_one] } },
    have hε₂ : 0 < ε₂ := sorry,

    let n := f m,
    obtain ⟨i', j', hi', rfl, n₁, hn₁⟩ :=
      hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (by linarith) n ε₁ hε₁,
    let p₁ := g n₁,
    obtain ⟨i'', j'', hi'', rfl, p₂, hp₂⟩ := hP _ hc _ (by sorry) p₁ ε₂ hε₂,
    obtain ⟨n₂, hn₂, hnormn₂⟩ := Hg c i'' (by sorry) p₂,
    let n₁' := N.d i'' i' n₂,
    obtain ⟨nnew₁, hnnew₁, hnormnnew₁⟩ := Hg c i' (by sorry) (g (res n₁ - n₁')),
    have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker := sorry,
    rw ← hg at hker,
    obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
    refine ⟨i', hi', m₁, _⟩,

    by_cases hizero : i = 0,
    { subst hizero,
      rw [nat.zero_sub] at hi',
      subst hi',
      rw [zero_add] at *,
      sorry },

    have hii' : i' + 1 = i,
    { rw [hi', nat.sub_one, nat.add_one, nat.succ_pred_eq_of_pos (zero_lt_iff.mpr hizero)] },
    have hfm : ∥g (N.d i' i n₁)∥ = ∥g (res (f m) - N.d i' i n₁)∥,
    { have : f (@res _ c₁ (k' * c) _ _ m) ∈ f.apply.range,
      { rw normed_group_hom.mem_range,
        exact ⟨res m, rfl⟩ },
      rw [hg, normed_group_hom.mem_ker] at this,
      change ∥g ((N.d i' i) n₁)∥ = ∥g.apply (res (f m) - (N.d i' i) n₁)∥,
      rw [res_apply, normed_group_hom.map_sub, this, zero_sub, norm_neg],
      refl },

    calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : ((hfker _ _).norm _).symm
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
      by rw [normed_group_hom.map_sub]
    ... ≤ ∥res n - N.d i' i n₁∥ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥ + ε₂) :
      add_le_add_right (hN_adm.res_norm_noninc _ _ _ _ _) _
    ... ≤ K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * ∥P.d i' (i' + 1) p₁∥ + ε₂) :
      add_le_add_right hn₁ _
    ... = K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * ∥P.d i' (i' + 1) (g n₁)∥ + ε₂) : rfl
    ... = K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * ∥g (N.d i' i n₁)∥ + ε₂) : by rw [← d_apply, hii']
    ... = K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) : by rw [hfm]
    ... ≤ K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) $ nnreal.coe_nonneg K') _) $ nnreal.coe_nonneg r₂) _
    ... = K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * r₁ * ∥res n - N.d i' i n₁∥ + ε₂) : by rw [mul_assoc]
    ... ≤ K * ∥N.d i (i + 1) n∥ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i + 1)) n∥ + ε₁) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg (nnreal.coe_nonneg K') (nnreal.coe_nonneg r₁)) _) $ nnreal.coe_nonneg r₂) _
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i + 1) n∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
    ... = Knew * ∥N.d i (i + 1) (f m)∥ + ε / 2 * (1 + K' * r₁ * r₂)⁻¹ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : rfl
    ... = Knew * ∥N.d i (i + 1) (f m)∥ + ε / 2 + r₂ * ε₂ :
      by rw [mul_assoc, inv_mul_cancel hneq, mul_one]
    ... ≤ Knew * ∥N.d i (i + 1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
    ... = Knew * ∥f (M.d i (i + 1) m)∥ + ε : by rw [add_assoc, add_halves', d_apply]
    ... = Knew * ∥f.apply (M.d i (i + 1) m)∥ + ε : rfl
    ... = Knew * ∥(M.d i (i + 1)) m∥ + ε : by rw (hfker _ _).norm _
  end
