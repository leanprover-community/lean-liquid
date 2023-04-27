import polyhedral_lattice.pseudo_normed_group
import pseudo_normed_group.splittable
import combinatorial_lemma.finite

.

open_locale big_operators nnreal
open pseudo_normed_group (filtration)

namespace polyhedral_lattice

variables (Λ : Type*) [polyhedral_lattice Λ]

example : pseudo_normed_group (Λ →+ ℤ) := by apply_instance

-- instance dual_nacg : normed_add_comm_group (Λ →+ ℤ) :=
-- _

theorem dual_polyhedral' [module.free ℤ Λ] :
  ∃ (ι : Type) [fintype ι] (f : ι → (Λ →+ ℤ)), by exactI
  ∀ g : Λ →+ ℤ, ∃ c : ι → ℕ, g = ∑ i, c i • f i ∧
    ∀ d : ι → ℝ≥0, (∀ i, (f i) ∈ filtration (Λ →+ ℤ) (d i)) →
      (g ∈ filtration (Λ →+ ℤ) (∑ i, c i • d i)) :=
begin
  obtain ⟨I, _inst_I, l, hl, hl'⟩ := polyhedral_lattice.polyhedral Λ, resetI,
  choose S hS using (λ ε : sign_vectors I, explicit_gordan (ε • l)),
  let ι := Σ ε, S ε,
  let e := fintype.equiv_fin ι,
  refine ⟨fin (fintype.card ι), infer_instance, λ k, (e.symm k).2, _⟩,
  intro g,
  let ε := pos_vector l g, specialize hS ε,
  sorry
end

theorem dual_polyhedral :
  ∃ (ι : Type) [fintype ι] (f : ι → (Λ →+ ℤ)), by exactI
  ∀ g : Λ →+ ℤ, ∃ c : ι → ℕ, g = ∑ i, c i • f i ∧
    ∀ d : ι → ℝ≥0, (∀ i, (f i) ∈ filtration (Λ →+ ℤ) (d i)) →
      (g ∈ filtration (Λ →+ ℤ) (∑ i, c i • d i)) :=
begin
  sorry
end

end polyhedral_lattice

theorem lem98_finite' (Λ : Type*) [polyhedral_lattice Λ] (M : Type*) [pseudo_normed_group M]
  (N : ℕ) [hN : fact (0 < N)] (d : ℝ≥0)
  (H : pseudo_normed_group.splittable M N d) :
  pseudo_normed_group.splittable (Λ →+ M) N (d * lem98.d (Λ →+ ℤ) N) :=
begin
  classical, constructor,
  let l := lem98.l Λ,
  have hl := lem98.hl Λ,
  have hl' := lem98.hl' Λ,
  let A := lem98.A Λ N,
  have hA := lem98.hA Λ N,
  let d := lem98.d Λ N,
  intros c x hx,
  -- `x` is a homomorphism `Λ →+ Lbar r' S`
  -- we split it into pieces `Λ →+ ℤ` for all coefficients indexed by `s` and `n`
  let x' : S → ℕ → Λ →+ ℤ := λ s n, (Lbar.coeff s n).comp x,
  have := λ s n, hA (x' s n), clear hA,
  choose x₁' hx₁' x₀' hx₀' H using this,
  have hx₀_aux : ∀ s n i, (x₀' s n (l i)).nat_abs ≤ (x (l i) s n).nat_abs :=
    (λ s n i, le_trans (le_add_right (nat.le_mul_of_pos_left hN.1)) (H s n i).ge),
  -- now we assemble `x₀' : S → ℕ → Λ →+ ℤ` into a homomorphism `Λ →+ Lbar r' S`
  let x₀ : Λ →+ Lbar r' S := Lbar.mk_aux hl x x₀' hx₀_aux,
  have hx₀ : x₀ ∈ filtration (Λ →+ Lbar r' S) (c / N) :=
    Lbar.mk_aux_mem_filtration _ _ _ hN.1 hl hx x₀' x₁' x' (λ _ _ _, rfl) H hx₀_aux,
  -- and similarly for `x₁'`
  let x₁ : Λ →+ Lbar r' S := Lbar.mk_aux hl x x₁'
    (λ s n i, le_trans (le_add_left le_rfl) (H s n i).ge),
  -- `x₁` can be written as a sum of tensors
  -- `x₁ = ∑ a in A, a ⊗ xₐ`, for some `xₐ : Lbar r' S`
  let xₐ : (Λ →+ ℤ) → Lbar r' S := λ a, Lbar.mk_of_add_monoid_hom x₁' a,
  have hx₁ : ∀ l, x₁ l = ∑ a in A, a l • xₐ a := lem_98_aux _ _ hx₁' _ (λ _ _ _, rfl),
  -- now it is time to start building `y`
  -- we first decompose the `xₐ a` into `N` pieces
  have hxₐ : ∀ a s n, (xₐ a s n).nat_abs ≤ 1,
  { intros a s n, dsimp [xₐ, Lbar.mk_of_add_monoid_hom_to_fun], split_ifs; simp },
  have := λ a, lem98_int N hN.1 ∥xₐ a∥₊ (xₐ a) _ (hxₐ a),
  swap 2, { rw Lbar.mem_filtration_iff },
  choose y' hy'1 hy'2 using this,
  -- the candidate `y` combines `x₀` together with the pieces `y'` of `xₐ a`
  let y : fin N → Λ →+ Lbar r' S := λ j, x₀ + ∑ a in A, Lbar.mk_tensor a (y' a j),
  have hxy : x = ∑ i, y i,
  { apply lem98_aux' N A x x₀ x₁ x' x₀' x₁' hx₀' _ _ _ hx₁ y' hy'1 y,
    all_goals { intros, refl } },
  use [y, hxy],
  intro j,
  rw hl.add_monoid_hom_mem_filtration_iff at hx ⊢,
  intro i,
  specialize hx i,
  simp only [Lbar.mem_filtration_iff] at hx hy'2 ⊢,
  have Hx : ∥x (l i)∥₊ = N • ∥x₀ (l i)∥₊ + ∑ a in A, ∥a (l i)∥₊ * ∥xₐ a∥₊,
  { apply lem98_crux N hN.1 A x x₀ x₁ x' x₀' x₁' xₐ,
    all_goals { intros, refl <|> apply_assumption } },
  calc ∥y j (l i)∥₊
      ≤ ∥x₀ (l i)∥₊ + ∑ a in A, ∥a (l i)∥₊ * ∥xₐ a∥₊ / N + d * ∥l i∥₊ : _
  ... = (N • ∥x₀ (l i)∥₊ + ∑ a in A, ∥a (l i)∥₊ * ∥xₐ a∥₊) / N + d * ∥l i∥₊ : _
  ... = ∥x (l i)∥₊ / N + d * ∥l i∥₊ : by rw Hx
  ... ≤ _ : _,
  { simp only [add_monoid_hom.add_apply, add_assoc, add_monoid_hom.finset_sum_apply,
         Lbar.mk_tensor_apply],
    refine (Lbar.nnnorm_add_le _ _).trans (add_le_add le_rfl _),
    refine (Lbar.nnnorm_sum_le _ _).trans _,
    calc ∑ a in A, ∥a (l i) • y' a j∥₊
        = ∑ a in A, ∥a (l i)∥₊ * ∥y' a j∥₊ : finset.sum_congr rfl _
    ... ≤ ∑ a in A, ∥a (l i)∥₊ * (∥xₐ a∥₊ / N + 1) : finset.sum_le_sum _
    ... = ∑ a in A, (∥a (l i)∥₊ * ∥xₐ a∥₊ / N + ∥a (l i)∥₊) : finset.sum_congr rfl _
    ... = ∑ a in A, (∥a (l i)∥₊ * ∥xₐ a∥₊ / N) + ∑ a in A, ∥a (l i)∥₊ : _
    ... ≤ ∑ a in A, (∥a (l i)∥₊ * ∥xₐ a∥₊ / N) + d * ∥l i∥₊ : add_le_add le_rfl _,
    { intros a ha, rw Lbar.nnnorm_zsmul },
    { intros a ha, exact mul_le_mul' le_rfl (hy'2 a j) },
    { intros a ha, rw [mul_add, mul_one, mul_div_assoc] },
    { rw finset.sum_add_distrib },
    { calc ∑ a in A, ∥a (l i)∥₊
          = (∑ a in A, ∥a (l i)∥₊ / ∥l i∥₊) * ∥l i∥₊ : _
      ... ≤ finset.univ.sup (λ i, ∑ a in A, ∥a (l i)∥₊ / ∥l i∥₊) * ∥l i∥₊ : _,
      { { have : ∥l i∥₊ ≠ 0, { simp only [hl' i, nnnorm_eq_zero, ne.def, not_false_iff] },
          simp only [div_eq_mul_inv, ← finset.sum_mul, inv_mul_cancel_right₀ this] } },
      { exact mul_le_mul' (finset.le_sup (finset.mem_univ i)) le_rfl } } },
  { simp only [div_eq_mul_inv, add_mul, finset.sum_mul, nsmul_eq_mul],
    congr' 2,
    rw [mul_comm, inv_mul_cancel_left₀],
    exact_mod_cast hN.1.ne' },
  { simp only [add_mul, div_eq_mul_inv],
    refine add_le_add _ le_rfl,
    rw [mul_right_comm],
    exact mul_le_mul' hx le_rfl }
end
