import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes


variables (M N P : system_of_complexes.{u}) (f : M ⟶ N) (g : N ⟶ P)

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma ε₁_pos (a : ℝ≥0) {ε ε₁ : ℝ} (hε : 0 < ε) (hmulε : ε₁ * (1 + a) = ε / 2) :
  0 < ε₁ :=
have one_add_pos : (0 : ℝ) < 1 + a := add_pos_of_pos_of_nonneg zero_lt_one (zero_le a),
calc 0 < ε / 2 / (1 + ↑a) : div_pos (half_pos hε) one_add_pos
   ... = _                : ((eq_div_iff one_add_pos.ne').mpr hmulε).symm

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma norm_sub_le_mul_norm_add {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
  ... = ∥res _ - (N.d i' i (res n₁) - N.d i' i (_ + nnew₁))∥ :
    by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
  ... = ∥(res _ - N.d i' i (res n₁)) + N.d i' i (_ + nnew₁)∥ : by abel
  ... ≤ ∥res _ - N.d i' i _∥ + ∥N.d i' i (_ + nnew₁)∥ : norm_add_le _ _
  ... = ∥res _ - N.d i' i _∥ + ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
  ... ≤ ∥res _ - N.d i' i _∥ + r₂ * ∥g (res n₁ - _)∥ :
    add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
  ... = ∥res _ - N.d i' i _∥ + r₂ * ∥res _ - P.d i'' i' (g n₂)∥ :
    by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply _ _ g,
      ←d_apply]
  ... ≤ ∥res _ - N.d i' i _∥ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
  ... = _ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
    by rw [←res_res, d_res, normed_group_hom.map_sub]
  ... ≤ K * _ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
    add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
  ... = K * _ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
    by rw [d_apply _ _ g _, hii', hfm]
  ... ≤ K * _ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg) _
  ... = K * _ + ε₁ + r₂ * (K' * r₁ * ∥res _ - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
  ... ≤ K * _ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) _∥ + ε₁) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg) _
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ :
    congr_arg (λ e, (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥(N.d i (i + 1)) (f m)∥ + e + ↑r₂ * ε₂) hmulε₁
  ... ≤ _ * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
  ... = _ * ∥(M.d i (i+1)) m∥ + ε : by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`.
The `ρ` in this lemma stands for `K + r₁ * r₂ * K * K'` in the application. -/
lemma exists_norm_sub_le_mul_add {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)) (ε : ℝ), 0 < ε →
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥ + ε)))
  (m₁ : (M (k * k' * c) i))
  {ε : ℝ}
  (hε : 0 < ε) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ + ε :=
begin
  haveI : fact (k * (k' * c) ≤ k * k' * c) := { out := (mul_assoc _ _ _).symm.le },
  rcases ex_le (res m₁) ε hε with ⟨i₀, rfl, y, hy⟩,
  rw [res_res, d_res] at hy,
  refine ⟨i - 1, _, rfl, rfl, _⟩,
  refine ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left _ ρ.2) ε)⟩,
  exact hM_adm.res_norm_noninc _ _ _ _ _,
end

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma norm_sub_le_mul_mul_norm_add {M N : system_of_complexes} {f : M ⟶ N}
  {k k' K c : ℝ≥0} (mK : ℝ≥0) {ε ε₁ : ℝ} {m : M (k * (k' * c)) 0} {n₁ : N (k' * c) 0} {m₁ : M c 0}
  (ee1 : ε₁ ≤ ε)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (inadm : ∥((res (res m : (M (k' * c) 0))) : (M c 0))∥ ≤ ∥(res m : (M (k' * c) 0))∥ )
  (hn₁ : ∥res (f m) - (N.d 0 0) n₁∥ ≤ ↑K * ∥(N.d 0 (0 + 1)) (f m)∥ + ε₁) :
  ∥res m - (M.d 0 0) m₁∥ ≤ (K * (1 + mK)) * ∥(M.d 0 (0 + 1)) m∥ + ε :=
begin
  simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
  rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
  have new : fact (c ≤ k' * c) := { out := le_mul_of_one_le_left c.2 hk'.out },
  rw ←res_res _ _ _ new,
  refine le_trans inadm (le_trans hn₁ _),
  rw [d_apply, hom_apply f _, hfnorm],
  refine add_le_add _ ee1,
  rw mul_assoc,
  refine (mul_le_mul_of_nonneg_left _ K.2),
  exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right mK.2),
end

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma ε₁_le_ε {ε ε₁ : ℝ} (hε : 0 < ε) (mK : ℝ≥0) (hε₁ : ε₁ = ε / 2 * (1 + mK)⁻¹) :
  ε₁ ≤ ε :=
by { rw [hε₁, div_eq_mul_inv, mul_assoc, ← mul_inv'],
     exact mul_le_of_le_one_right hε.le (inv_le_one $ nnreal.coe_le_coe.mpr $
      one_le_mul one_le_two $ le_add_of_nonneg_right mK.2) }

lemma weak_normed_snake_dual (k k' K K' r₁ r₂ : ℝ≥0)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {a : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_weak_bounded_exact k K (a + 1) c₀)
  (hP : P.is_weak_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnrm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_weak_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
begin
  introsI c hc i hi,
  apply exists_norm_sub_le_mul_add (admissible_of_isometry hN_adm hf),
  intros m ε hε,

  have hlt : 0 < (1 + K' * r₁ * r₂ : ℝ) :=
    add_pos_of_pos_of_nonneg zero_lt_one ((K' * r₁ * r₂).coe_nonneg),
  have hε₁ : 0 < ε / 2 * (1 + K' * r₁ * r₂)⁻¹ := mul_pos (half_pos hε) (inv_pos.2 hlt),
  obtain ⟨_, _, rfl, rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (f m) _ hε₁,
  have Hi' : i - 1 ≤ a + 1 := trans i.pred_le (trans hi a.le_succ),
  obtain ⟨_, _, rfl, rfl, p₂, hp₂⟩ := hP _ hc _ Hi' (g n₁)
    (if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹) _,
  { --revert ε,
    extract_goal,
    have Hi'' : (i - 1 - 1) ≤ a + 1 + 1 := trans (nat.pred_le _) (trans Hi' (nat.le_succ _)),
    obtain ⟨n₂, rfl, hnormn₂⟩ := Hg c (i - 1 - 1) Hi'' p₂,
    let n₁' := N.d (i - 1 - 1) (i - 1) n₂,
    obtain ⟨nnew₁, hnnew₁, hnrmnew₁⟩ := Hg c (i - 1) (trans Hi' a.succ.le_succ) (g (res n₁ - n₁')),
    have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
    { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ←hom_apply, ←hom_apply, hnnew₁] },
    rw ←hg at hker,
    obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
    refine ⟨i - 1, rfl, m₁, _⟩,

    have hfnrm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ :=
      λ c i x, (isometry_iff_norm _).1 (hf c i) x,
    by_cases hizero : i = 0,
    { subst hizero,
      convert norm_sub_le_mul_mul_norm_add (K' * r₁ * r₂) _ hfnrm _ hn₁,
      { norm_cast, ring },
      { exact ε₁_le_ε hε (K' * r₁ * r₂) rfl },
      { exact (admissible_of_isometry hN_adm hf).res_norm_noninc _ _ _ _ _ } },

    { refine norm_sub_le_mul_norm_add M N P f g _ hN_adm hgnrm hfnrm _ _ hn₁ hp₂ hnrmnew₁ hm₁ _,
      { exact nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hizero) },
      { field_simp [hlt.ne.symm], ring },
      { by_cases H : r₂ = 0,
        { simp only [H, nnreal.coe_zero, if_true, zero_mul, (half_pos hε).le], },
        { simp only [H, nnreal.coe_eq_zero, if_false, mul_comm,
            mul_inv_cancel_left' (nnreal.coe_ne_zero.mpr H)] } },
      { have : f (res m : M (k' * c) i) ∈ f.apply.range, { rw mem_range, exact ⟨res m, rfl⟩ },
        rw [hg, mem_ker] at this,
        rw [hom_apply g (res (f m) - (N.d (i - 1) i) n₁), res_apply, normed_group_hom.map_sub, this,
          zero_sub, norm_neg, ←hom_apply] } } },
  { by_cases H : r₂ = 0,
    { simp only [H, zero_lt_one, if_true, eq_self_iff_true, nnreal.coe_eq_zero] },
    { simp only [H, nnreal.coe_eq_zero, if_false],
      exact mul_pos (half_pos hε) (inv_pos.2 (nnreal.coe_pos.2 (zero_lt_iff.2 H))) } }
end

/-  I (DT) extracted this lemma to speed up the proof of `normed_snake_dual`.
The `ρ` in this lemma stands for `K + r₁ * r₂ * K * K'` in the application. -/
lemma exists_norm_sub_le_mul {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)),
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥)))
  (m₁ : (M (k * k' * c) i)) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ :=
begin
  haveI : fact (k * (k' * c) ≤ k * k' * c) := { out := (mul_assoc _ _ _).symm.le },
  rcases ex_le (res m₁) with ⟨i₀, rfl, y, hy⟩,
  rw [res_res, d_res] at hy,
  refine ⟨i - 1, _, rfl, rfl, _⟩,
  refine ⟨y, hy.trans (mul_le_mul_of_nonneg_left _ ρ.2)⟩,
  exact hM_adm.res_norm_noninc _ _ _ _ _,
end

/-  I (DT) extracted this lemma to speed up the proof of `normed_snake_dual`. -/
lemma norm_sub_le_mul_mul_norm {M N : system_of_complexes} {f : M ⟶ N}
  {k k' K c : ℝ≥0} (mK : ℝ≥0) {m : M (k * (k' * c)) 0} {n₁ : N (k' * c) 0} {m₁ : M c 0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (inadm : ∥((res (res m : (M (k' * c) 0))) : (M c 0))∥ ≤ ∥(res m : (M (k' * c) 0))∥ )
  (hn₁ : ∥res (f m) - (N.d 0 0) n₁∥ ≤ ↑K * ∥(N.d 0 (0 + 1)) (f m)∥) :
  ∥res m - (M.d 0 0) m₁∥ ≤ (K * (1 + mK)) * ∥(M.d 0 (0 + 1)) m∥ :=
begin
  simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
  rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
  have new : fact (c ≤ k' * c) := { out := le_mul_of_one_le_left c.2 hk'.out },
  rw ←res_res _ _ _ new,
  refine le_trans inadm (le_trans hn₁ _),
  rw [d_apply, hom_apply f _, hfnorm],
  rw mul_assoc,
  refine (mul_le_mul_of_nonneg_left _ K.2),
  exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right mK.2),
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
  introsI c hc i hi,
  refine exists_norm_sub_le_mul (admissible_of_isometry hN_adm hf) _,

  intro m,

  obtain ⟨_, _, rfl, rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (f m),
  have Hi' : (i - 1) ≤ a + 1 := trans i.pred_le (trans hi a.le_succ),
  obtain ⟨_, _, rfl, rfl, p₂, hp₂⟩ := hP _ hc _ Hi' (g n₁),
  have Hi'' : (i - 1 - 1) ≤ a + 1 + 1 := trans (nat.pred_le _) (trans Hi' (nat.le_succ _)),
  obtain ⟨n₂, rfl, hnormn₂⟩ := Hg c (i - 1 - 1) Hi'' p₂,
  let n₁' := N.d (i - 1 - 1) (i - 1) n₂,
  obtain ⟨nnew₁, hnnew₁, hnormnnew₁⟩ := Hg c (i - 1) (trans Hi' (nat.le_succ _)) (g (res n₁ - n₁')),
  have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
  { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ←hom_apply, ←hom_apply, hnnew₁] },
  rw ←hg at hker,
  obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
  refine ⟨i - 1, rfl, m₁, _⟩,

  have hfnorm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ := λ c i x, (isometry_iff_norm _).1 (hf c i) x,
  by_cases hizero : i = 0,
  { subst hizero,
    convert norm_sub_le_mul_mul_norm (K' * r₁ * r₂) hfnorm _ hn₁,
    { norm_cast, ring },
    { exact (admissible_of_isometry hN_adm hf).res_norm_noninc _ _ _ _ _ } },

  have hii' : i - 1 + 1 = i,
  { rw [nat.sub_one, nat.add_one, nat.succ_pred_eq_of_pos (zero_lt_iff.mpr hizero)] },
  have hfm : ∥g (N.d (i - 1) i n₁)∥ = ∥g (res (f m) - N.d (i - 1) i n₁)∥,
  { have : f (@res _ _ (k' * c) _ _ m) ∈ f.apply.range := by { rw mem_range, exact ⟨res m, rfl⟩ },
    rw [hg, mem_ker] at this,
    rw [hom_apply g (res (f m) - (N.d _ i) n₁), res_apply, normed_group_hom.map_sub, this,
      zero_sub, norm_neg, ←hom_apply] },
  rw ← add_zero (_ * ∥_∥) at ⊢ hn₁ hp₂,
  apply norm_sub_le_mul_norm_add M N P f g hii' hN_adm hgnorm hfnorm _ _ hn₁ hp₂ hnormnnew₁ hm₁ hfm;
  simp,
end
