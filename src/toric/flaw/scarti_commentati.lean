--def dual_set_generators (s : set M) : set N := { n : N | }

--lemma dual_fg_of_finite {s : set M} (fs : s.finite) : (f.dual_set P₀ s).fg :=
--sorry

/-
/--  The behaviour of `dual_set` under smultiplication. -/
lemma dual_smul {s : set M} {r : R₀} {m : M} :
  f.dual_set P₀ (s.insert m) ≤ f.dual_set P₀ (s.insert (r • m)) :=
begin
  intros n hn m hm,
  rcases hm with rfl | hm,
  { rw [linear_map.map_smul_of_tower, linear_map.smul_apply],
    exact P₀.smul_mem r (hn m (s.mem_insert m)) },
  { exact hn _ (set.mem_insert_iff.mpr (or.inr hm)) }
end
-/

/-
def to_linear_dual (f : pairing R M N R) : N →ₗ[R] (M →ₗ[R] R) :=
{ to_fun := λ n,
  { to_fun := λ m, f m n,
    map_add' := λ x y, by simp only [linear_map.add_apply, linear_map.map_add],
    map_smul' := λ x y, by simp only [linear_map.smul_apply, linear_map.map_smul] },
  map_add' := λ x y, by simpa only [linear_map.map_add],
  map_smul' := λ r n, by simpa only [algebra.id.smul_eq_mul, linear_map.map_smul] }

lemma to_ld (f : pairing R M N R) (n : N) : to_linear_dual f n = mul_right f n := rfl

-- this lemma requires some extra hypotheses: at the very least, some finite-generation
-- condition: the "standard" scalar product on `ℝ ^ (⊕ ℕ)` has power-series as its dual
-- but is non-degenerate.
/-- A pairing `f` between two `R`-modules `M` and `N` with values in `R` is perfect if every
linear function `l : M →ₗ[R] R` is represented as -/
lemma left_nondegenerate_exists {f : pairing R M N R} (r : right_nondegenerate f) :
  ∀ l : M →ₗ[R] R, ∃ n : N, ∀ m : M, l m = f m n :=
begin
  intros l,
  sorry,
end
-/

--variables {M N : Type*} [add_comm_monoid M] --[semimodule ℕ M] [semimodule ℤ M]
  --[algebra ℕ ℤ] [is_scalar_tower ℕ ℤ M]

--variables {P : Type*}
--  [add_comm_monoid N] --[semimodule ℕ N] [semimodule ℤ N] --[is_scalar_tower ℕ ℤ N]
--  [add_comm_monoid P] --[semimodule ℕ P] [semimodule ℤ P] --[is_scalar_tower ℕ ℤ P]
--  (P₀ : submodule ℕ P)

/-
lemma pointed_of_is_basis {ι : Type*} (v : ι → M) (bv : is_basis R v) :
  pointed R (submodule.span R₀ (set.range v)) :=
begin
  obtain ⟨l, hl⟩ : ∃ l : M →ₗ[R] R, ∀ i : ι, l (v i) = 1 :=
    ⟨bv.constr (λ _, 1), λ i, constr_basis bv⟩,
  refine Exists.intro
  { to_fun := ⇑l,
    map_add' := by simp only [forall_const, eq_self_iff_true, linear_map.map_add],
    map_smul' := λ m x, by
    { rw [algebra.id.smul_eq_mul, linear_map.map_smul],
      refine congr _ rfl,
      exact funext (λ y, by simp only [has_scalar.smul, gsmul_int_int]) } } _,
  rintros m hm (m0 : l m = 0),
  obtain ⟨c, csup, rfl⟩ := span_as_sum hm,
  simp_rw [linear_map.map_sum] at m0,--, linear_map.map_smul_of_tower] at m0,
  have : linear_map.compatible_smul M R R₀ R := sorry,
  conv_lhs at m0 {
    apply_congr, skip, rw @linear_map.map_smul_of_tower _ _ _ _ _ _ _ _ _ _ _ this l, skip },
  have : ∑ (i : M) in c.support, (c i • l i : R) = ∑ (i : M) in c.support, (c i : R),
  { refine finset.sum_congr rfl (λ x hx, _),
    rcases set.mem_range.mp (set.mem_of_mem_of_subset (finset.mem_coe.mpr hx) csup) with ⟨i, rfl⟩,
    simp [hl _, (•)], },
  rw this at m0,
  have : ∑ (i : M) in c.support, (0 : M) = 0,
  { rw finset.sum_eq_zero,
    simp only [eq_self_iff_true, forall_true_iff] },
  rw ← this,
  refine finset.sum_congr rfl (λ x hx, _),
  rw finset.sum_eq_zero_iff_of_nonneg at m0,
  { rw [int.coe_nat_eq_zero.mp (m0 x hx), zero_smul] },
  { exact λ x hx, int.coe_nat_nonneg _ }
end
-/

--[semimodule ℕ M]
-- [semimodule ℤ M]
--variables {M N : Type*} [add_comm_monoid M] --[semimodule ℕ M] [semimodule ℤ M]
  --[algebra ℕ ℤ] [is_scalar_tower ℕ ℤ M]

--variables {P : Type*}
--  [add_comm_monoid N] --[semimodule ℕ N] [semimodule ℤ N] --[is_scalar_tower ℕ ℤ N]
--  [add_comm_monoid P] --[semimodule ℕ P] [semimodule ℤ P] --[is_scalar_tower ℕ ℤ P]
--  (P₀ : submodule ℕ P)

/- This might be junk
def standard_pairing_Z : pairing ℤ ℤ ℤ ℤ :=
{ to_fun := λ z,
  { to_fun := λ n, z * n,
    map_add' := mul_add z,
    map_smul' := λ m n, algebra.mul_smul_comm m z n },
  map_add' := λ x y, by simpa [add_mul],
  map_smul' := λ x y, by simpa only [algebra.smul_mul_assoc] }

lemma nond_Z : right_nondegenerate standard_pairing_Z :=
λ m hm, eq.trans (mul_one m).symm (hm 1)


def standard_pairing_Z_sq : pairing ℤ (ℤ × ℤ) (ℤ × ℤ) ℤ :=
{ to_fun := λ z,
  { to_fun := λ n, z.1 * n.1 + z.2 * n.2,
    map_add' := λ x y, by { rw [prod.snd_add, prod.fst_add], ring },
    map_smul' := λ x y,
      by simp only [smul_add, algebra.mul_smul_comm, prod.smul_snd, prod.smul_fst] },
  map_add' := λ x y, begin
    congr,
    ext,
    dsimp,
    rw [prod.snd_add, prod.fst_add, add_mul],
    ring,
  end,
  map_smul' := λ x y, begin
    congr,
    simp only [smul_add, prod.smul_snd, linear_map.coe_mk, prod.smul_fst, algebra.smul_mul_assoc],
  end }

lemma nond_Z_sq : right_nondegenerate standard_pairing_Z_sq :=
begin
  refine λ  m hm, prod.ext _ _,
  { obtain (F : m.fst * (1 : ℤ) + m.snd * (0 : ℤ) = 0) := hm (1, 0),
    simpa using F },
  { obtain (F : m.fst * (0 : ℤ) + m.snd * (1 : ℤ) = 0) := hm (0, 1),
    simpa using F }
end

lemma fd (v : fin 2 → ℤ × ℤ) (ind : linear_independent ℤ v) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
begin
  refine ⟨_, _⟩,
  convert mul_right standard_pairing_Z_sq (v 0 + v 1),
--  convert @mul_right ℤ (ℤ × ℤ) _ _ _ (ℤ × ℤ) ℤ _ _ _ _ standard_pairing_Z_sq ((1, 1) : ℤ × ℤ),
  intros m hm m0,
  induction m with m1 m2,
  congr,

--  tidy?,

  refine (mul_right standard_pairing_Z_sq ((1, 1) : ℤ × ℤ) : ℤ × ℤ →ₗ[ℤ] ℤ),
--  refine ((λ m : ℤ × ℤ, standard_pairing_Z_sq m (1,1)) : ℤ × ℤ →ₗ[ℤ] ℤ),
  refine
  { to_fun := λ m, standard_pairing_Z_sq m (1,1),
    map_add' :=
      by simp only [forall_const, eq_self_iff_true, linear_map.add_apply, linear_map.map_add],
    map_smul' := λ x m, begin
      rw [standard_pairing_Z_sq, algebra.id.smul_eq_mul, linear_map.map_smul, linear_map.coe_mk, linear_map.coe_mk],
      simp only [has_scalar.smul, gsmul_int_int, linear_map.coe_mk],
  end },
  simp at *, fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { intros ᾰ, cases ᾰ }, work_on_goal 1 { intros x y, cases y, cases x, dsimp at * }, work_on_goal 2 { intros m x, cases x, dsimp at * } }, work_on_goal 3 { intros x ᾰ ᾰ_1, cases x, dsimp at *, simp at *, simp at *, fsplit, work_on_goal 0 { assumption } },
  { refl },
  { simp [(•)] },

  convert pointed_of_sub_R M,
end

#exit

lemma fd {ι : Type*} (s : finset ι) (v : ι → ℤ × ℤ) (ind : linear_independent ℤ v) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
begin
  refine ⟨_, _⟩,
  convert mul_right standard_pairing_Z_sq (∑ a in s, v a),
--  convert @mul_right ℤ (ℤ × ℤ) _ _ _ (ℤ × ℤ) ℤ _ _ _ _ standard_pairing_Z_sq ((1, 1) : ℤ × ℤ),
  intros m hm m0,
  induction m with m1 m2,
  congr,

--  tidy?,

  refine (mul_right standard_pairing_Z_sq ((1, 1) : ℤ × ℤ) : ℤ × ℤ →ₗ[ℤ] ℤ),
--  refine ((λ m : ℤ × ℤ, standard_pairing_Z_sq m (1,1)) : ℤ × ℤ →ₗ[ℤ] ℤ),
  refine
  { to_fun := λ m, standard_pairing_Z_sq m (1,1),
    map_add' :=
      by simp only [forall_const, eq_self_iff_true, linear_map.add_apply, linear_map.map_add],
    map_smul' := λ x m, begin
      rw [standard_pairing_Z_sq, algebra.id.smul_eq_mul, linear_map.map_smul, linear_map.coe_mk, linear_map.coe_mk],
      simp only [has_scalar.smul, gsmul_int_int, linear_map.coe_mk],
  end },
  simp at *, fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { intros ᾰ, cases ᾰ }, work_on_goal 1 { intros x y, cases y, cases x, dsimp at * }, work_on_goal 2 { intros m x, cases x, dsimp at * } }, work_on_goal 3 { intros x ᾰ ᾰ_1, cases x, dsimp at *, simp at *, simp at *, fsplit, work_on_goal 0 { assumption } },
  { refl },
  { simp [(•)] },

  convert pointed_of_sub_R M,
end

lemma fd {ι : Type*} (v : ι → ℤ × ℤ) (ind : linear_independent ℤ v) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
begin
  refine ⟨_, _⟩,
  convert mul_right standard_pairing_Z_sq (1, 1),
--  convert @mul_right ℤ (ℤ × ℤ) _ _ _ (ℤ × ℤ) ℤ _ _ _ _ standard_pairing_Z_sq ((1, 1) : ℤ × ℤ),
  intros m hm m0,

  refine (mul_right standard_pairing_Z_sq ((1, 1) : ℤ × ℤ) : ℤ × ℤ →ₗ[ℤ] ℤ),
--  refine ((λ m : ℤ × ℤ, standard_pairing_Z_sq m (1,1)) : ℤ × ℤ →ₗ[ℤ] ℤ),
  refine
  { to_fun := λ m, standard_pairing_Z_sq m (1,1),
    map_add' :=
      by simp only [forall_const, eq_self_iff_true, linear_map.add_apply, linear_map.map_add],
    map_smul' := λ x m, begin
      rw [standard_pairing_Z_sq, algebra.id.smul_eq_mul, linear_map.map_smul, linear_map.coe_mk, linear_map.coe_mk],
      simp only [has_scalar.smul, gsmul_int_int, linear_map.coe_mk],
  end },
  simp at *, fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { intros ᾰ, cases ᾰ }, work_on_goal 1 { intros x y, cases y, cases x, dsimp at * }, work_on_goal 2 { intros m x, cases x, dsimp at * } }, work_on_goal 3 { intros x ᾰ ᾰ_1, cases x, dsimp at *, simp at *, simp at *, fsplit, work_on_goal 0 { assumption } },
  { refl },
  { simp [(•)] },

  convert pointed_of_sub_R M,
end



lemma pointed_of_sub_Z {ι : Type*} (v : ι → ℤ) (ind : linear_independent ℤ v) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
by convert pointed_of_sub_R ℤ

lemma fd {ι : Type*} (v : ι → M) (ind : linear_independent ℤ v) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
begin
  tidy?,
  convert pointed_of_sub_R M,
end
-/
