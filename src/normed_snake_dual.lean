import system_of_complexes.basic


/-!
# The normed snake dual lemma: weak and non-weak

This file proves the weak normed snake dual lemma and the normed snake dual lemma: they are the
statements `weak_normed_snake_dual` and `normed_snake_dual`, respectively.

The principal definitions of the concepts in this file appear in Section 4 of the blueprint.

The two main results prove `is_(weak_)bounded_exact` for certain `system_of_complexes`.  The
Lean-definitions of these concepts appears in `system_of_complexes.basic`.

Intuitively, the two predicates assert a form of exactness for a complex in the form of an
inequality of the form
```
∥res ? - (M.d ??) ?∥ ≤ const * ∥(M.d ?? ?∥ + ε.
```
(Recall that `res` is a restriction among certain complexes, `M.d` stands for a differential,
`const` is a constant; the error `ε` is a non-negative real number.  For the weak version, we
quantify over all `0 < ε ∈ ℝ`.  For the non-weak version, we use `ε = 0`.)

More in detail, at the heart of the computation, is a proof of an inequality of the form
```lean
∥res m - (M.d (i - 1) i) y∥ ≤ K * (1 + K' * r₁ * r₂) * ∥(M.d i (i + 1)) m∥ + ε.
```
For the weak normed snake dual lemma, for any choice of positive `0 < ε`, we should be able to fix
the parameters so that the inequality above is satisfied.  For the normed snake dual lemma, we want
the inequality above with `ε = 0`.  As you will see, the bulk of the proof of the normed snake dual
lemma recycles the proof of the weak version.


The proof involves several estimations: we broke these proofs into smaller partial inequalities,
for two reasons.  First, it streamlines the formalization.  Second, it helps Lean processing the
statements, reducing processing times.

# Remark

While following the proof, keep an eye out for how the factor `ρ = 1 + K' * r₁ * r₂` forms itself.
Once the factor `ρ` is formed, we can almost treat it as a new strictly positive variable.
-/

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes

variables {M N P : system_of_complexes.{u}} {f : M ⟶ N} {g : N ⟶ P}

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma ε₁_le_ε {ε ε₁ : ℝ} (hε : 0 ≤ ε) (mK : ℝ≥0) (hε₁ : ε₁ = ε / 2 * (1 + mK)⁻¹) :
  ε₁ ≤ ε :=
by { rw [hε₁, div_eq_mul_inv, mul_assoc, ← mul_inv'],
     exact mul_le_of_le_one_right hε (inv_le_one $ nnreal.coe_le_coe.mpr $
      one_le_mul one_le_two $ le_add_of_nonneg_right mK.2) }

/-!
First, we break off the main term `∥res m - (M.d i' i) m₁∥` into a sum of two expressions:

* `∥(res (f m) : N c i) - N.d i' i (res n₁)∥`, and
* `∥(N.d i' i ((N.d i'' i') n₂ + nnew₁) : N c i)∥`.
-/
lemma norm_sub_le_split {k' c c₁ : ℝ≥0} {i i' i'' : ℕ}
  [hk' : fact (1 ≤ k')] [fc : fact (c ≤ c₁)]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'} {n₂ : N c i''} {nnew₁ : N c i'} {m₁ : M c i'} {m : (M c₁ i)}
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁) :
  ∥res m - (M.d i' i) m₁∥ ≤
    ∥(res (f m) : N c i) - N.d i' i (res n₁)∥ + ∥(N.d i' i ((N.d i'' i') n₂ + nnew₁) : N c i)∥ :=
calc ∥res m - (M.d i' i) m₁∥
      = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
  ... = ∥res (f m) - (N.d i' i (res n₁) - N.d i' i ((N.d i'' i') n₂ + nnew₁))∥ :
    by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
  ... = ∥(res (f m) - N.d i' i (res n₁)) + N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ :
    by rw [sub_eq_add_neg, neg_sub, sub_eq_neg_add, ← add_assoc, ← sub_eq_add_neg]
  ... ≤ ∥res (f m) - N.d i' i (res n₁)∥ + ∥N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ : norm_add_le _ _

/-!
We then massage the left-hand side.  The proof of this lemma is deceptively simple, since
there is a lot of typeclass work happening in the background.  In particular, the `c` in the sea of
underscores of the second line is crucial.

(The hypothesis `(hN_adm : N.admissible)` is only used via `(hN_adm.res_norm_noninc _ c _ _ _)`,
producing the inequality
`(dis : ∥(res (res (f m) - (N.d i' i) n₁) : N c i)∥ ≤ ∥res (f m) - (N.d i' i) n₁∥)`.)
-/
lemma norm_sub_le_mul_norm_add_lhs {k' K c c₁ : ℝ≥0} {ε₁ : ℝ} {i i' : ℕ}
  [hk' : fact (1 ≤ k')] [fc₁ : fact (k' * c ≤ c₁)] [fc : fact (c ≤ c₁)]
  {n₁ : N (k' * c) i'} {m : (M c₁ i)}
  (hN_adm : N.admissible)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁) :
  ∥(res (f m) : N c i) - N.d i' i (res n₁)∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ :=
calc ∥(res (f m) : N c i) - N.d i' i (res n₁)∥
      = ∥res (res (f m) - (N.d i' i) n₁)∥ : by rw [normed_group_hom.map_sub, d_res, ← res_res]
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁  : trans (hN_adm.res_norm_noninc _ c _ _ _) hn₁

/-!
And we also massage the right-hand side.  Here, the factor `K' * r₁ * r₂` appears.

(The hypothesis `(hN_adm : N.admissible)` is only used via `(hN_adm.d_norm_noninc _ _ i' i nnew₁)`,
producing the inequality `(dis : ∥(N.d i' i) nnew₁∥ ≤ ∥nnew₁∥)`.)
-/
lemma norm_sub_le_mul_norm_add_rhs {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')] [fc₁ : fact (k' * c ≤ c₁)]
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  {n₁ : N (k' * c) i'} {n₂ : N c i''} {nnew₁ : N c i'} {m : (M c₁ i)}
  (hN_adm : N.admissible)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥(N.d i' i ((N.d i'' i') n₂ + nnew₁) : N c i)∥ ≤
    K * K' * r₁ * r₂ * ∥(N.d i (i+1)) (f m)∥ + K' * r₁ * r₂ * ε₁ + r₂ * ε₂ :=
calc ∥(N.d i' i ((N.d i'' i') n₂ + nnew₁) : N c i)∥
      = ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
  ... ≤ r₂ * ∥g (res n₁ - (N.d i'' i') n₂)∥ : trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁
  ... = r₂ * ∥res (g n₁) - P.d i'' i' (g n₂)∥ :
    by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply _ _ g, ←d_apply]
  ... ≤ r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) : mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg
  ... = r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) : by rw [d_apply _ _ g _, hii', hfm]
  ... ≤ r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
    mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg
  ... = r₂ * (K' * r₁ * ∥res (f m) - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
  ... ≤ r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) (f m)∥ + ε₁) + ε₂) :
    mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg
  ... = _ : by ring

/-!
We collect the inequalities obtained so far.  Use `norm_sub_le_split` to split the norm into a sum
of two contribution:

* apply `norm_sub_le_mul_norm_add_lhs` to the left-hand-side;
* apply `norm_sub_le_mul_norm_add_rhs` to the right-hand-side.

The rest is simple manipulations of real numbers.
-/
lemma norm_sub_le_mul_norm_add {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')] [fc₁ : fact (k' * c ≤ c₁)] [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'} {n₂ : N c i''} {nnew₁ : N c i'} {m₁ : M c i'} {m : (M c₁ i)}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
calc
∥res m - (M.d i' i) m₁∥ ≤ ∥res (f m) - N.d i' i (res n₁)∥ + ∥N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ :
    norm_sub_le_split hfnorm hm₁
  ... ≤ (K * ∥(N.d i (i + 1)) (f m)∥ + ε₁) +
        (K * K' * r₁ * r₂ * ∥(N.d i (i+1)) (f m)∥ + K' * r₁ * r₂ * ε₁ + r₂ * ε₂) : add_le_add
      (norm_sub_le_mul_norm_add_lhs hN_adm hn₁)
      (norm_sub_le_mul_norm_add_rhs hii' hgnorm hN_adm hn₁ hp₂ hnormnnew₁ hfm)
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ :
    congr_arg (λ e, (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥(N.d i (i + 1)) (f m)∥ + e + ↑r₂ * ε₂) hmulε₁
  ... ≤ (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
  ... = (K + r₁ * r₂ * K * K') * ∥(M.d i (i+1)) m∥ + ε :
    by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]

/-!
We shall apply this lemma with `ρ = K + r₁ * r₂ * K * K' = K * (1 + K' * r₁ * r₂)`.
-/
lemma exists_norm_sub_le_mul_add {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)) (ε : ℝ), 0 < ε →
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥ + ε)))
  {m₁ : (M (k * k' * c) i)}
  {ε : ℝ} (hε : 0 < ε) :
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

/-!
This argument proves the main inequality in the case where the indices are `0` or `1`.
-/
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

/-!
Note that `ε = 0` is allowed.  Indeed, the weak normed snake dual lemma uses `0 ≤ ε`, while the
normed snake dual lemma uses `ε = 0`.
-/
lemma exist_norm_sub_le_mul_norm_add {k k' K K' r₁ r₂ c₀ c : ℝ≥0}
  {a i : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hN_adm : N.admissible)
  (hgnrm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [_inst_1 : fact (c₀ ≤ c)] (i : ℕ),
          i ≤ a + 1 + 1 → ∀ (y : (P c i)), ∃ (x : (N c i)), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ (c : ℝ≥0) (i : ℕ), (range f.apply : add_subgroup (N c i)) = ker g.apply)
  (hf : ∀ (c : ℝ≥0) (i : ℕ), (isometry (f.apply : M c i ⟶ N c i) : _))
  (hc : fact (c₀ ≤ c))
  (hi : i ≤ a)
  {m : M (k * (k' * c)) i} {n₁ : N (k' * c) (i - 1)}
  (hn₁ : ∥res (f m) - (N.d (i - 1) i) n₁∥ ≤
    K * ∥(N.d i (i + 1)) (f m)∥ + ε / 2 * (1 + K' * r₁ * r₂)⁻¹)
  (Hi' : i - 1 ≤ a + 1)
  (p₂ : P c (i - 1 - 1)) (hp₂ : ∥res (g n₁) - (P.d (i - 1 - 1) (i - 1)) p₂∥ ≤
    K' * ∥(P.d (i - 1) (i - 1 + 1)) (g n₁)∥ + ite (r₂ = 0) 1 (ε / 2 * (r₂)⁻¹)) :
  ∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
    ∥res m - (M.d i₀ i) y∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
begin
  obtain ⟨n₂, rfl, hnormn₂⟩ :=
    Hg c (i - 1 - 1) (trans (nat.pred_le _) (trans Hi' (nat.le_succ _))) p₂,
  let n₁' := N.d (i - 1 - 1) (i - 1) n₂,
  obtain ⟨nnew₁, hnnew₁, hnrmnew₁⟩ := Hg c (i - 1) (trans Hi' a.succ.le_succ) (g (res n₁ - n₁')),
  have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
  { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ←hom_apply, ←hom_apply, hnnew₁] },
  rw ←hg at hker,
  obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
  refine ⟨i - 1, rfl, m₁, _⟩,
  have hfnrm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ := λ c i x, (isometry_iff_norm _).1 (hf c i) x,
  by_cases hizero : i = 0,
  { subst hizero,
    convert norm_sub_le_mul_mul_norm_add (K' * r₁ * r₂) _ hfnrm _ hn₁,
    { norm_cast, ring },
    { exact ε₁_le_ε hε (K' * r₁ * r₂) rfl },
    { exact (admissible_of_isometry hN_adm hf).res_norm_noninc _ _ _ _ _ } },
  { refine norm_sub_le_mul_norm_add _ hN_adm hgnrm hfnrm _ _ hn₁ hp₂ hnrmnew₁ hm₁ _,
    { exact nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hizero) },
    { rw inv_mul_cancel_right',
      exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (zero_le (K' * r₁ * r₂))) },
    { by_cases H : r₂ = 0,
      { simp only [H, nnreal.coe_zero, if_true, zero_mul, (div_nonneg hε zero_le_two)] },
      { simp only [H, nnreal.coe_eq_zero, if_false, mul_comm,
          mul_inv_cancel_left' (nnreal.coe_ne_zero.mpr H)] } },
    { have : f (res m : M (k' * c) i) ∈ f.apply.range, { rw mem_range, exact ⟨res m, rfl⟩ },
      rw [hg, mem_ker] at this,
      rw [hom_apply g (res (f m) - (N.d (i - 1) i) n₁), res_apply, normed_group_hom.map_sub, this,
        zero_sub, norm_neg, ←hom_apply] } }
end

/-!
We apply this lemma with `ρ = K + r₁ * r₂ * K * K'`.
-/
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

variables (M N P f g)

/-!
Finally, we can state and prove the weak normed snake dual lemma.
-/
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

  have hε₁ : 0 < ε / 2 * (1 + K' * r₁ * r₂)⁻¹ := mul_pos (half_pos hε)
    (inv_pos.2 $ add_pos_of_pos_of_nonneg zero_lt_one ((K' * r₁ * r₂).coe_nonneg)),
  obtain ⟨_, _, rfl, rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (f m) _ hε₁,
  have Hi' : i - 1 ≤ a + 1 := trans i.pred_le (trans hi a.le_succ),
  obtain ⟨_, _, rfl, rfl, p₂, hp₂⟩ := hP _ hc _ Hi' (g n₁)
    (if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹) _,
  { simp_rw [nnreal.coe_eq_zero r₂] at hp₂,
    apply exist_norm_sub_le_mul_norm_add hε.le hN_adm hgnrm Hg hg hf hc hi hn₁ Hi' p₂,
    convert hp₂, },
  { by_cases H : r₂ = 0,
    { simp only [H, zero_lt_one, if_true, eq_self_iff_true, nnreal.coe_eq_zero] },
    { simp only [H, nnreal.coe_eq_zero, if_false],
      exact mul_pos (half_pos hε) (inv_pos.2 (nnreal.coe_pos.2 (zero_lt_iff.2 H))) } }
end

/-!
And also the normed snake dual lemma.
-/
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
  rw ← add_zero (_ * ∥_∥) at ⊢,
  have hn₁₁ :  ∥res (f m) - (N.d (i - 1) i) n₁∥ ≤
    K * ∥(N.d i (i + 1)) (f m)∥ + 0 / 2 * (1 + K' * r₁ * r₂)⁻¹, rwa [zero_div, zero_mul, add_zero],
  obtain F := exist_norm_sub_le_mul_norm_add rfl.le hN_adm hgnorm Hg hg hf hc hi hn₁₁ Hi' p₂,
  by_cases hr : r₂ = 0,
  { subst hr,
    simp at ⊢ F,
    exact F (trans hp₂ (le_add_of_nonneg_right zero_le_one)) },
  { exact F (by { convert hp₂, simp [hr] } ) }
end
