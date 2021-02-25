import algebra.group.basic
import normed_group.NormedGroup

import Mbar.basic
import polyhedral_lattice.basic
import normed_group.pseudo_normed_group

/-!
In this file we state and prove lemmas 9.7 and 9.8 of [Analytic].
-/

open_locale nnreal big_operators

section lem97

variables (Λ : Type*) [add_comm_group Λ]

lemma le_or_le {α : Type*} [linear_order α] (a b : α) :
  a ≤ b ∨ b ≤ a :=
(le_or_lt a b).imp id le_of_lt

lemma abs_add_eq_add_abs_iff (a b : ℤ) :
  abs (a + b) = abs a + abs b ↔ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) :=
begin
  sorry
end

/-
jmc: I don't know exactly which version of the two lemmas below
will be easier to prove, `lem97` or `lem97'`.
The first one is closer to [Analytic], but the second one is easier to use.
Mathematically they are indistinguishable.
-/

/-- Lemma 9.7 of [Analytic]. -/
lemma lem97 (hΛ_tf : torsion_free Λ) [hΛ_fg : module.finite ℤ Λ]
  {ι : Type*} [fintype ι]
  (N : ℕ) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (0 ≤ x' (l i) ∧ 0 ≤ (x - x') (l i)) ∨ (x' (l i) ≤ 0 ∧ (x - x') (l i) ≤ 0) :=
begin
  sorry
end

/-- Lemma 9.7 of [Analytic]. -/
lemma lem97' (hΛ_tf : torsion_free Λ) [hΛ_fg : module.finite ℤ Λ]
  {ι : Type*} [fintype ι]
  (N : ℕ) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (x (l i)).nat_abs = N * (y (l i)).nat_abs + (x' (l i)).nat_abs :=
begin
  sorry
end

end lem97

open pseudo_normed_group


variables (Λ : Type*) (r' : ℝ≥0) (S : Type*)
variables [fintype S] [normed_group Λ] [polyhedral_lattice Λ]

section

variables {S}

-- move this
@[simps]
def Mbar.coeff (s : S) (n : ℕ) : Mbar r' S →+ ℤ :=
{ to_fun := λ x, x s n,
  map_zero' := rfl,
  map_add' := λ x y, rfl }

-- move this
@[simp] lemma nnreal.coe_nat_abs (n : ℤ) : ↑n.nat_abs = nnnorm n :=
nnreal.eq $
calc ((n.nat_abs : ℝ≥0) : ℝ)
    = ↑(n.nat_abs : ℤ) : by simp only [int.cast_coe_nat, nnreal.coe_nat_cast]
... = abs n            : by simp only [← int.abs_eq_nat_abs, int.cast_abs]
... = ∥n∥               : rfl

-- move this
@[simp] lemma pi.nat_apply {α β : Type*} [has_zero β] [has_one β] [has_add β] :
  ∀ (n : ℕ), (n : α → β) = λ _, n
| 0     := rfl
| (n+1) := show (n + 1 : α → β) = λ _, n + 1, by { rw pi.nat_apply, refl }
.

variables {Λ r'}

-- ugly name
def Mbar.mk_aux
  {ι : Type} [fintype ι] {l : ι → Λ} (hl : generates_norm l)
  (x : Λ →+ Mbar r' S) (y : S → ℕ → Λ →+ ℤ)
  (h : ∀ s n i, (y s n (l i)).nat_abs ≤ (x (l i) s n).nat_abs) :
  Λ →+ Mbar r' S :=
add_monoid_hom.mk' (λ l',
{ to_fun := λ s n, y s n l',
  coeff_zero' := λ s,
  begin
    obtain ⟨d, hd, c, h1, h2⟩ := hl l',
    suffices : y s 0 (d • l') = 0,
    { rw [← nsmul_eq_smul, add_monoid_hom.map_nsmul, nsmul_eq_mul,
        mul_eq_zero, int.nat_cast_eq_coe_nat, int.coe_nat_eq_zero] at this,
      exact this.resolve_left hd.ne' },
    rw [h1, add_monoid_hom.map_sum, finset.sum_eq_zero],
    rintro i -,
    suffices : y s 0 (l i) = 0,
    { rw [← nsmul_eq_smul, add_monoid_hom.map_nsmul, this, nsmul_zero] },
    specialize h s 0 i,
    simpa only [int.nat_abs_eq_zero, Mbar.coeff_zero, le_zero_iff, int.nat_abs_zero] using h
  end,
  summable' :=
  begin
    intro s,
    obtain ⟨d, hd, c, h1, h2⟩ := hl.generates_nnnorm l',
    suffices : summable (λ n, ↑(y s n (d • l')).nat_abs * r' ^ n),
    { refine nnreal.summable_of_le _ this,
      intro n,
      refine mul_le_mul' _ le_rfl,
      rw [← nsmul_eq_smul, add_monoid_hom.map_nsmul, nsmul_eq_mul,
        int.nat_abs_mul, int.nat_cast_eq_coe_nat, int.nat_abs_of_nat],
      norm_cast,
      exact nat.le_mul_of_pos_left hd },
    rw h1,
    suffices : summable (λ n, ∑ i, c i • ↑(y s n (l i)).nat_abs * r' ^ n),
    { apply nnreal.summable_of_le _ this,
      intro n,
      rw ← finset.sum_mul,
      refine mul_le_mul' _ le_rfl,
      simp only [add_monoid_hom.map_sum, ← nsmul_eq_smul, nnreal.coe_nat_abs,
        add_monoid_hom.map_nsmul],
      refine le_trans (nnnorm_sum_le _ _) (le_of_eq (fintype.sum_congr _ _ _)),
      intro i,
      simp only [nsmul_eq_mul, int.nat_cast_eq_coe_nat, ← nnreal.coe_nat_abs,
        int.nat_abs_mul, int.nat_abs_of_nat, nat.cast_mul] },
    apply summable_sum,
    rintro i -,
    apply nnreal.summable_of_le _ ((c i • x (l i)).summable s),
    intro n,
    apply mul_le_mul' _ le_rfl,
    simp only [← nsmul_eq_smul, nsmul_eq_mul, int.nat_cast_eq_coe_nat,
      ← nnreal.coe_nat_abs, int.nat_abs_mul, int.nat_abs_of_nat, ← nat.cast_mul,
        Mbar.coe_nsmul, pi.mul_apply, pi.nat_apply, @pi.nat_apply ℕ ℤ _ _ _ (c i)],
    norm_cast,
    exact nat.mul_le_mul le_rfl (h _ _ _)
  end }) $ λ l₁ l₂, by { ext s n, exact (y s n).map_add l₁ l₂ }

section pseudo_normed_group

variables (M : Type*) [pseudo_normed_group M]

def pseudo_normed_group.archimedean : Prop :=
∀ (m : M) (c : ℝ≥0) (n : ℕ), 0 < n →
  ((n • m) ∈ filtration M (n • c) ↔ m ∈ filtration M c)

lemma Mbar.archimedean : pseudo_normed_group.archimedean (Mbar r' S) :=
begin
  intros x c N hN,
  simp only [Mbar.mem_filtration_iff],
  have hN' : 0 < (N : ℝ≥0) := by exact_mod_cast hN,
  conv_rhs { rw ← mul_le_mul_left hN' },
  simp only [← nsmul_eq_smul, nsmul_eq_mul, finset.mul_sum, finset.sum_mul,
    Mbar.coe_nsmul, pi.mul_apply, pi.nat_apply, @pi.nat_apply ℕ ℤ _ _ _ N,
    int.nat_abs_mul, int.nat_abs_of_nat, int.nat_cast_eq_coe_nat, nat.cast_mul],
  convert iff.rfl,
  ext s,
  simp only [nnreal.coe_nat_cast, nnreal.coe_tsum, nnreal.coe_mul,
    ← tsum_mul_left, ← mul_assoc],
end

lemma pseudo_normed_group.archimedean.add_monoid_hom
  (h : pseudo_normed_group.archimedean M) :
  pseudo_normed_group.archimedean (Λ →+ M) :=
begin
  intros f c N hN,
  apply forall_congr, intro c,
  apply forall_congr, intro l,
  apply forall_congr, intro hl,
  simp only [← nsmul_eq_smul, nsmul_eq_mul, mul_assoc],
  simp only [nsmul_eq_smul, ← nsmul_eq_mul, add_monoid_hom.nat_smul_apply],
  exact h _ _ N hN
end

variables {M}

-- move this
lemma pseudo_normed_group.smul_mem_filtration (n : ℕ) (m : M) (c : ℝ≥0)
  (h : m ∈ filtration M c) :
  (n • m) ∈ filtration M (n • c) :=
begin
  induction n with n ih, { simpa only [zero_smul] using zero_mem_filtration _ },
  simp only [nat.succ_eq_add_one, add_smul, one_smul],
  exact add_mem_filtration ih h,
end

lemma generates_norm.add_monoid_hom_mem_filtration_iff {ι : Type} [fintype ι]
  {l : ι → Λ} (hl : generates_norm l) (hM : pseudo_normed_group.archimedean M)
  (x : Λ →+ M) (c : ℝ≥0) :
  x ∈ filtration (Λ →+ M) c ↔
  ∀ c' i, (l i) ∈ filtration Λ c' → x (l i) ∈ filtration M (c * c') :=
begin
  refine ⟨λ H c' i h, H h, _⟩,
  intros H c' l' hl',
  obtain ⟨d, hd, cᵢ, h1, h2⟩ := hl.generates_nnnorm l',
  rw [← hM _ _ d hd, ← nsmul_eq_smul, ← x.map_nsmul, nsmul_eq_smul, h1, x.map_sum],
  refine filtration_mono _ (sum_mem_filtration _ (λ i, c * cᵢ i * nnnorm (l i)) _ _),
  { calc ∑ i, c * cᵢ i * nnnorm (l i)
        = c * ∑ i, cᵢ i * nnnorm (l i) : by simp only [mul_assoc, ← finset.mul_sum]
    ... = c * (d * nnnorm l') : by rw h2
    ... ≤ c * (d * c') : mul_le_mul' le_rfl (mul_le_mul' le_rfl hl')
    ... = d • (c * c') : by rw [← nsmul_eq_smul, nsmul_eq_mul, mul_left_comm] },
  rintro i -,
  convert pseudo_normed_group.smul_mem_filtration (cᵢ i) _ _
    (H (nnnorm (l i)) i (le_refl (nnnorm (l i)))),
  { rw [← nsmul_eq_smul, x.map_nsmul, nsmul_eq_smul] },
  { rw [← nsmul_eq_smul, nsmul_eq_mul, mul_left_comm, mul_assoc] }
end

end pseudo_normed_group

end

variables {Λ r' S}

@[simps]
def Mbar.mk_of_add_monoid_hom (x : S → ℕ → Λ →+ ℤ) (a : Λ →+ ℤ)
  [∀ s n, decidable (x s n = a)] :
  Mbar r' S :=
{ to_fun := λ s n, if x s n = a ∧ 0 < n then 1 else 0,
  coeff_zero' := λ s, by simp only [not_lt_zero', and_false, if_false],
  summable' :=
  begin
    intro s,
    have := (normed_ring.summable_geometric_of_norm_lt_1 (r' : ℝ) _), swap,
    { rwa nnreal.norm_eq },
    simp only [← nnreal.coe_pow, nnreal.summable_coe] at this,
    apply nnreal.summable_of_le _ this,
    intro n,
    refine (mul_le_mul' _ le_rfl).trans (one_mul _).le,
    split_ifs; simp
  end }

lemma Mbar.mk_aux_mem_filtration
  (ι : Type) (c : ℝ≥0) (N : ℕ) (hN : 0 < N) [fintype ι]
  {l : ι → Λ} (hl : generates_norm l)
  {x : Λ →+ Mbar r' S}
  (hx : x ∈ filtration (Λ →+ Mbar r' S) c)
  (x₀' : S → ℕ → Λ →+ ℤ)
  (x₁' : S → ℕ → Λ →+ ℤ)
  (x' : S → ℕ → Λ →+ ℤ)
  (hx' : ∀ l s n, x l s n = x' s n l)
  (H : ∀ s n i, (x' s n (l i)).nat_abs =
    N * (x₀' s n (l i)).nat_abs + (x₁' s n (l i)).nat_abs)
  (H' : ∀ s n i, (x₀' s n (l i)).nat_abs ≤ (x (l i) s n).nat_abs) :
  Mbar.mk_aux hl x x₀' H' ∈ filtration (Λ →+ Mbar r' S) (c / ↑N) :=
begin
  set x₀ := Mbar.mk_aux hl x x₀' H',
  refine (Mbar.archimedean.add_monoid_hom _ _ _ _ hN).mp _,
  have aux : N • (c / N) = c,
  { rw [← nsmul_eq_smul, nsmul_eq_mul, mul_comm, div_mul_cancel],
    exact_mod_cast hN.ne' },
  rw aux,
  rw hl.add_monoid_hom_mem_filtration_iff Mbar.archimedean at hx ⊢,
  intros c' i hli,
  specialize hx c' i hli,
  rw Mbar.mem_filtration_iff at hx ⊢,
  refine le_trans (finset.sum_le_sum _) hx,
  rintro s -,
  refine tsum_le_tsum _ (((N • x₀) (l i)).summable s) ((x (l i)).summable s),
  intro n,
  refine mul_le_mul' _ le_rfl,
  norm_cast,
  simp only [add_monoid_hom.nat_smul_apply],
  simp only [← nsmul_eq_smul, Mbar.coe_nsmul, nsmul_eq_mul,
    pi.mul_apply, pi.nat_apply, @pi.nat_apply ℕ ℤ _ _ _ N,
    int.nat_cast_eq_coe_nat, int.nat_abs_mul, int.nat_abs_of_nat],
  convert le_trans (le_add_right le_rfl) (H s n i).ge,
  apply hx'
end

lemma Mbar.mk_tensor (a : Λ →+ ℤ) (x : Mbar r' S) :
  Λ →+ Mbar r' S :=
add_monoid_hom.mk' (λ l, a l • x) $ λ l₁ l₂, by rw [a.map_add, add_smul]

-- better name?
lemma lem_98_aux (A : finset (Λ →+ ℤ))
  (x₁' : S → ℕ → Λ →+ ℤ) [∀ s n a, decidable (x₁' s n = a)]
  (hx₁' : ∀ s n, x₁' s n ∈ A) (x₁ : Λ →+ Mbar r' S)
  (hx₁ : ∀ l s n, x₁ l s n = x₁' s n l) (l : Λ) :
  x₁ l = ∑ a in A, a l • Mbar.mk_of_add_monoid_hom x₁' a :=
begin
  ext s n,
  simp only [finset.sum_apply, Mbar.coe_sum, pi.smul_apply, Mbar.coe_smul,
    Mbar.coe_mk],
  rw [finset.sum_eq_single (x₁' s n)],
  { simp only [true_and, and_congr, if_congr, eq_self_iff_true,
          Mbar.mk_of_add_monoid_hom_to_fun],
    split_ifs with hn,
      { simp only [← gsmul_eq_smul, mul_one, gsmul_int_int, hx₁] },
      { rw [smul_zero],
        obtain rfl : n = 0 := nat.eq_zero_of_le_zero (le_of_not_lt hn),
        exact (x₁ l).coeff_zero s } },
  { intros a haA ha,
    simp only [ha.symm, false_and, if_false, smul_zero,
      Mbar.mk_of_add_monoid_hom_to_fun] },
  { intro hsn, exact (hsn (hx₁' s n)).elim }
end

lemma lem98_int [fact (r' < 1)] (N : ℕ) (hN : 0 < N) (c : ℝ≥0)
  (x : Mbar r' S) (hx : x ∈ filtration (Mbar r' S) c)
  (H : ∀ s n, (x s n).nat_abs ≤ 1) :
  ∃ y : fin N → Mbar r' S, (x = ∑ i, y i) ∧
      (∀ i, y i ∈ filtration (Mbar r' S) (c/N + 1)) :=
begin
  sorry
end

lemma lem98 [fact (r' < 1)] (N : ℕ) (hN : 0 < N) :
  ∃ d, ∀ c (x : Λ →+ Mbar r' S) (hx : x ∈ filtration (Λ →+ Mbar r' S) c),
    ∃ y : fin N → (Λ →+ Mbar r' S),
      (x = ∑ i, y i) ∧
      (∀ i, y i ∈ filtration (Λ →+ Mbar r' S) (c/N + d)) :=
begin
  classical,
  obtain ⟨ι, _ftι, l, hl⟩ := polyhedral_lattice.polyhedral Λ, resetI,
  obtain ⟨A, hA⟩ := lem97' Λ polyhedral_lattice.tf N l,
  let d := finset.univ.sup (λ i, ∑ a in A, (a (l i)).nat_abs),
  use d,
  intros c x hx,
  -- `x` is a homomorphism `Λ →+ Mbar r' S`
  -- we split it into pieces `Λ →+ ℤ` for all coefficients indexed by `s` and `n`
  let x' : S → ℕ → Λ →+ ℤ := λ s n, (Mbar.coeff r' s n).comp x,
  have := λ s n, hA (x' s n), clear hA,
  choose x₁' hx₁' x₀' hx₀' H using this,
  have hx₀_aux : ∀ s n i, (x₀' s n (l i)).nat_abs ≤ (x (l i) s n).nat_abs :=
    (λ s n i, le_trans (le_add_right (nat.le_mul_of_pos_left hN)) (H s n i).ge),
  -- now we assemble `x₀' : S → ℕ → Λ →+ ℤ` into a homomorphism `Λ →+ Mbar r' S`
  let x₀ : Λ →+ Mbar r' S := Mbar.mk_aux hl x x₀' hx₀_aux,
  have hx₀ : x₀ ∈ filtration (Λ →+ Mbar r' S) (c / N) :=
    Mbar.mk_aux_mem_filtration _ _ _ hN hl hx x₀' x₁' x' (λ _ _ _, rfl) H hx₀_aux,
  -- and similarly for `x₁'`
  let x₁ : Λ →+ Mbar r' S := Mbar.mk_aux hl x x₁'
    (λ s n i, le_trans (le_add_left le_rfl) (H s n i).ge),
  -- `x₁` can be written as a sum of tensors
  -- `x₁ = ∑ a in A, a ⊗ xₐ`, for some `xₐ : Mbar r' S`
  let xₐ : (Λ →+ ℤ) → Mbar r' S := λ a, Mbar.mk_of_add_monoid_hom x₁' a,
  have hx₁ : ∀ l, x₁ l = ∑ a in A, a l • xₐ a := lem_98_aux _ _ hx₁' _ (λ _ _ _, rfl),
  -- now it is time to start building `y`
  -- we first decompose the `xₐ a` into `N` pieces
  have := λ a, lem98_int N hN _ (xₐ a) _ _,
  swap 3, { rw Mbar.mem_filtration_iff }, swap,
  { intros s n, dsimp [xₐ, Mbar.mk_of_add_monoid_hom_to_fun], split_ifs; simp },
  choose y' hy'1 hy'2 using this,
  -- the candidate `y` combines `x₀` together with the pieces `y'` of `xₐ a`
  let y : fin N → Λ →+ Mbar r' S :=
    λ j, x₀ + ∑ a in A, Mbar.mk_tensor a (y' a j),
  use y,
  split,
  { sorry },
  { sorry }
end
