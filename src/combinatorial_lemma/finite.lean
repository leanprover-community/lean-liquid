import analysis.normed.group.SemiNormedGroup.kernels

import Lbar.basic
import normed_group.pseudo_normed_group
import combinatorial_lemma.partition
import combinatorial_lemma.lem97
import polyhedral_lattice.pseudo_normed_group
import pseudo_normed_group.splittable

import hacks_and_tricks.by_exactI_hack

/-!
In this file we state and prove 9.8 of [Analytic].
-/

noncomputable theory

open_locale nnreal big_operators

open pseudo_normed_group combinatorial_lemma

variables (Λ : Type*) (r' : ℝ≥0) (S : Type*)
variables [fintype S] [polyhedral_lattice Λ]

section

variables {S Λ r'}

-- ugly name
@[simps]
def Lbar.mk_aux'
  (x : Λ →+ Lbar r' S) (y : S → ℕ → Λ →+ ℤ)
  (h : ∀ s n l, (y s n l).nat_abs ≤ (x l s n).nat_abs) :
  Λ →+ Lbar r' S :=
add_monoid_hom.mk' (λ l,
{ to_fun := λ s n, y s n l,
  coeff_zero' := λ s,
  begin
    specialize h s 0 l,
    simpa only [int.nat_abs_eq_zero, Lbar.coeff_zero, le_zero_iff, int.nat_abs_zero] using h
  end,
  summable' :=
  begin
    intro s,
    apply nnreal.summable_of_le _ ((x l).summable s),
    intro n,
    refine mul_le_mul' _ le_rfl,
    norm_cast,
    exact (h _ _ _)
  end }) $ λ l₁ l₂, by { ext s n, exact (y s n).map_add l₁ l₂ }

-- jmc: It seems to me that we cannot easily define this using `Lbar.mk_aux'` above
@[simps]
def Lbar.mk_aux
  {ι : Type} [fintype ι] {l : ι → Λ} (hl : generates_norm l)
  (x : Λ →+ Lbar r' S) (y : S → ℕ → Λ →+ ℤ)
  (h : ∀ s n i, (y s n (l i)).nat_abs ≤ (x (l i) s n).nat_abs) :
  Λ →+ Lbar r' S :=
add_monoid_hom.mk' (λ l',
{ to_fun := λ s n, y s n l',
  coeff_zero' := λ s,
  begin
    obtain ⟨c, h1, -⟩ := hl l',
    rw [h1, add_monoid_hom.map_sum, finset.sum_eq_zero],
    rintro i -,
    suffices : y s 0 (l i) = 0,
    { rw [add_monoid_hom.map_nsmul, this, nsmul_zero] },
    specialize h s 0 i,
    simpa only [int.nat_abs_eq_zero, Lbar.coeff_zero, le_zero_iff, int.nat_abs_zero] using h
  end,
  summable' :=
  begin
    intro s,
    obtain ⟨c, h1, -⟩ := hl.generates_nnnorm l',
    rw h1,
    suffices : summable (λ n, ∑ i, c i • ↑(y s n (l i)).nat_abs * r' ^ n),
    { apply nnreal.summable_of_le _ this,
      intro n,
      rw ← finset.sum_mul,
      refine mul_le_mul' _ le_rfl,
      simp only [add_monoid_hom.map_sum, nnreal.coe_nat_abs, add_monoid_hom.map_nsmul],
      refine le_trans (nnnorm_sum_le _ _) (le_of_eq (fintype.sum_congr _ _ _)),
      intro i,
      simp only [nsmul_eq_mul, ← nnreal.coe_nat_abs,
        int.nat_abs_mul, int.nat_abs_of_nat, nat.cast_mul] },
    apply summable_sum,
    rintro i -,
    apply nnreal.summable_of_le _ ((c i • x (l i)).summable s),
    intro n,
    refine mul_le_mul' _ le_rfl,
    simp only [nsmul_eq_mul, ← nnreal.coe_nat_abs, int.nat_abs_mul,
        int.nat_abs_of_nat, ← nat.cast_mul, Lbar.coe_nsmul, pi.mul_apply, pi.nat_apply],
    norm_cast,
    exact nat.mul_le_mul le_rfl (h _ _ _)
  end }) $ λ l₁ l₂, by { ext s n, exact (y s n).map_add l₁ l₂ }

end

variables {Λ r' S}

lemma Lbar.mk_aux_mem_filtration
  (ι : Type) (c : ℝ≥0) (N : ℕ) (hN : 0 < N) [fintype ι]
  {l : ι → Λ} (hl : generates_norm l)
  {x : Λ →+ Lbar r' S}
  (hx : x ∈ filtration (Λ →+ Lbar r' S) c)
  (x₀' : S → ℕ → Λ →+ ℤ)
  (x₁' : S → ℕ → Λ →+ ℤ)
  (x' : S → ℕ → Λ →+ ℤ)
  (hx' : ∀ l s n, x l s n = x' s n l)
  (H : ∀ s n i, (x' s n (l i)).nat_abs =
    N * (x₀' s n (l i)).nat_abs + (x₁' s n (l i)).nat_abs)
  (H' : ∀ s n i, (x₀' s n (l i)).nat_abs ≤ (x (l i) s n).nat_abs) :
  Lbar.mk_aux hl x x₀' H' ∈ filtration (Λ →+ Lbar r' S) (c / ↑N) :=
begin
  set x₀ := Lbar.mk_aux hl x x₀' H',
  have aux : c = (N : ℝ≥0) * (c / N),
  { rw [mul_comm, div_mul_cancel],
    exact_mod_cast hN.ne' },
  have hN' : (0: ℝ≥0) < N,
  {  exact_mod_cast hN },
  rw hl.add_monoid_hom_mem_filtration_iff at hx ⊢,
  intro i,
  specialize hx i,
  rw Lbar.mem_filtration_iff at hx ⊢,
  rw [← mul_le_mul_left hN', ← mul_assoc, ← aux, ← nsmul_eq_mul, ← Lbar.nnnorm_nsmul],
  refine le_trans (finset.sum_le_sum _) hx,
  rintro s -,
  refine tsum_le_tsum _ (Lbar.summable _ s) ((x (l i)).summable s),
  intro n,
  refine mul_le_mul' _ le_rfl,
  norm_cast,
  convert le_trans (le_add_right le_rfl) (H s n i).ge,
  swap, { apply hx' },
  rw [← int.nat_abs_of_nat N, ← int.nat_abs_mul, int.nat_abs_of_nat, ← nsmul_eq_mul],
  congr' 1,
end

@[simps]
def Lbar.mk_of_add_monoid_hom [fact (r' < 1)] (x : S → ℕ → Λ →+ ℤ) (a : Λ →+ ℤ)
  [∀ s n, decidable (x s n = a)] :
  Lbar r' S :=
Lbar.of_mask (Lbar.geom r' S) $ λ s n, x s n = a

@[simps apply]
def Lbar.mk_tensor (a : Λ →+ ℤ) (x : Lbar r' S) : Λ →+ Lbar r' S :=
add_monoid_hom.mk' (λ l, a l • x) $ λ l₁ l₂, by rw [a.map_add, add_smul]

-- better name?
lemma lem_98_aux [fact (r' < 1)] (A : finset (Λ →+ ℤ))
  (x₁' : S → ℕ → Λ →+ ℤ) [∀ s n a, decidable (x₁' s n = a)]
  (hx₁' : ∀ s n, x₁' s n ∈ A) (x₁ : Λ →+ Lbar r' S)
  (hx₁ : ∀ l s n, x₁ l s n = x₁' s n l) (l : Λ) :
  x₁ l = ∑ a in A, a l • Lbar.mk_of_add_monoid_hom x₁' a :=
begin
  ext s n,
  simp only [finset.sum_apply, Lbar.coe_sum, pi.smul_apply, Lbar.coe_zsmul,
    Lbar.coe_mk],
  rw [finset.sum_eq_single (x₁' s n)],
  { simp only [true_and, and_congr, if_congr, eq_self_iff_true, if_true,
          Lbar.mk_of_add_monoid_hom_to_fun],
    split_ifs with hn,
    { rw [smul_eq_mul, mul_zero, hn], exact (x₁ l).coeff_zero s },
    { simp only [smul_eq_mul, mul_one, hx₁] } },
  { intros a haA ha,
    simp only [ha.symm, false_and, if_false, smul_eq_mul, mul_zero,
      Lbar.mk_of_add_monoid_hom_to_fun] },
  { intro hsn, exact (hsn (hx₁' s n)).elim }
end

lemma fintype_prod_nat_equiv_nat (S : Type*) [fintype S] [hS : nonempty S] :
  nonempty (S × ℕ ≃ ℕ) :=
begin
  classical,
  obtain e' := fintype.equiv_fin S,
  refine nonempty.intro _,
  calc S × ℕ ≃ fin (fintype.card S) × ℕ : equiv.prod_congr_left (λ _, e')
         ... ≃ ℕ : classical.choice $ cardinal.eq.1 _,
  rw [← cardinal.lift_id (cardinal.mk ℕ),
    cardinal.mk_prod, ← cardinal.aleph_0, cardinal.mul_eq_right];
  simp [le_of_lt (cardinal.nat_lt_aleph_0 _), le_refl],
  rw ← fintype.card_pos_iff at hS,
  exact_mod_cast hS.ne'
end

lemma lem98_int [fact (r' < 1)] (N : ℕ) (hN : 0 < N) (c : ℝ≥0)
  (x : Lbar r' S) (hx : x ∈ filtration (Lbar r' S) c)
  (H : ∀ s n, (x s n).nat_abs ≤ 1) :
  ∃ y : fin N → Lbar r' S, (x = ∑ i, y i) ∧
      (∀ i, y i ∈ filtration (Lbar r' S) (c/N + 1)) :=
begin
  by_cases hS : nonempty S, swap,
  { refine ⟨λ i, 0, _, _⟩,
    { ext s n, exact (hS ⟨s⟩).elim },
    { intro, exact zero_mem_filtration _ } },
  resetI,
  obtain ⟨e⟩ := fintype_prod_nat_equiv_nat S,
  let f : ℕ → ℝ≥0 :=
    λ n, ↑(x (e.symm n).1 (e.symm n).2).nat_abs * r' ^ (e.symm n).2,
  have summable_f : summable f,
  { rw [← e.summable_iff, ← (equiv.sigma_equiv_prod S ℕ).summable_iff],
    simp only [function.comp, f, e.symm_apply_apply, nnreal.summable_sigma,
      equiv.sigma_equiv_prod_apply],
    -- TODO, missing lemma `fintype.summable`
    exact ⟨x.summable, ⟨_, has_sum_fintype _⟩⟩ },
  have f_aux : ∀ n, f n ≤ 1,
  { intro n,
    calc f n ≤ 1 * 1 : mul_le_mul' _ _
    ... = 1 : mul_one 1,
    { exact_mod_cast (H _ _) },
    { have : fact (r' < 1) := ‹_›, exact pow_le_one _ zero_le' this.out.le } },
  obtain ⟨mask, h1, h2⟩ := exists_partition N hN f f_aux summable_f,
  classical,
  let y := λ i, Lbar.of_mask x (λ s n, (e (s, n)) ∈ mask i),
  have hxy : x = ∑ i, y i,
  { ext s n,
    simp only [Lbar.coe_sum, if_congr, function.curry_apply, fintype.sum_apply,
      function.comp_app, Lbar.of_mask_to_fun, finset.sum_congr],
    obtain ⟨i, hi1, hi2⟩ := h1 (e (s, n)),
    rw [finset.sum_eq_single i, if_pos hi1],
    { rintro j - hj,
      rw if_neg,
      exact mt (hi2 j) hj },
    { intro hi, exact (hi (finset.mem_univ i)).elim } },
  refine ⟨y, hxy, _⟩,
  intro i,
  rw [Lbar.mem_filtration_iff] at hx ⊢,
  suffices : ∥x∥₊ = ∑' n, f n ∧ ∥y i∥₊ = ∑' (n : ℕ), (mask i).indicator f n,
  { calc ∥y i∥₊ = ∑' (n : ℕ), (mask i).indicator f n : this.right
            ... ≤ (∑' (n : ℕ), f n) / N + 1         : h2 i
            ... ≤ c / N + 1                         : _,
    simp only [div_eq_mul_inv],
    refine add_le_add (mul_le_mul' _ le_rfl) le_rfl,
    exact this.left.ge.trans hx },
  split,
  { calc ∑ s, ∑' n, ↑(x s n).nat_abs * r' ^ n
        = ∑' s, ∑' n, ↑(x s n).nat_abs * r' ^ n : (tsum_fintype _).symm
    ... = _ : _
    ... = ∑' n, f n : e.tsum_eq _,
    rw [← (equiv.sigma_equiv_prod S ℕ).tsum_eq], swap, { apply_instance },
    dsimp only [f, equiv.sigma_equiv_prod_apply],
    simp only [equiv.symm_apply_apply],
    rw [tsum_sigma'],
    { exact x.summable },
    { rw nnreal.summable_sigma, exact ⟨x.summable, ⟨_, has_sum_fintype _⟩⟩ } },
  { calc ∑ s, ∑' n, ↑(y i s n).nat_abs * r' ^ n
        = ∑' s, ∑' n, ↑(y i s n).nat_abs * r' ^ n : (tsum_fintype _).symm
    ... = ∑' x, (mask i).indicator f (e x) : _
    ... = ∑' n, (mask i).indicator f n : e.tsum_eq _,
    rw [← (equiv.sigma_equiv_prod S ℕ).tsum_eq], swap, { apply_instance },
    have aux : ∀ i s n h1, @ite _ (e (s, n) ∈ mask i) h1 (↑(x s n).nat_abs * r' ^ n) 0 =
      ↑(@ite _ (e (s, n) ∈ mask i) h1 (x s n) 0).nat_abs * r' ^ n,
    { intros, split_ifs; simp only [int.nat_abs_zero, nat.cast_zero, zero_mul, eq_self_iff_true] },
    dsimp only [f, y, set.indicator, equiv.sigma_equiv_prod_apply],
    simp only [equiv.symm_apply_apply, Lbar.of_mask_to_fun, aux],
    rw [tsum_sigma'],
    { exact (y i).summable },
    { rw nnreal.summable_sigma,
      exact ⟨(y i).summable, ⟨_, has_sum_fintype _⟩⟩ } }
end

lemma lem98_aux' [fact (r' < 1)] (N : ℕ)
  (A : finset (Λ →+ ℤ))
  (x x₀ x₁ : Λ →+ Lbar r' S)
  (x' x₀' x₁' : S → ℕ → Λ →+ ℤ) [∀ s n a, decidable (x₁' s n = a)]
  (H : ∀ s n, x' s n = N • x₀' s n + x₁' s n)
  (hx : ∀ l s n, x l s n = x' s n l)
  (hx₀ : ∀ l s n, x₀ l s n = x₀' s n l)
  (hx₁ : ∀ l s n, x₁ l s n = x₁' s n l)
  (Hx₁ : ∀ (l : Λ), x₁ l = ∑ (a : Λ →+ ℤ) in A, a l • Lbar.mk_of_add_monoid_hom x₁' a)
  (y' : (Λ →+ ℤ) → fin N → Lbar r' S)
  (hy' : ∀ (a : Λ →+ ℤ), Lbar.mk_of_add_monoid_hom x₁' a = finset.univ.sum (y' a))
  (y : fin N → Λ →+ Lbar r' S)
  (hy : ∀ i, y i = x₀ + ∑ a in A, Lbar.mk_tensor a (y' a i)) :
  x = ∑ (i : fin N), y i :=
begin
  intros,
  ext l s n,
  simp only [hx, H, hy, ← hx₁, Hx₁, hy', Lbar.coe_add, finset.sum_apply, add_monoid_hom.add_apply,
    Lbar.coe_sum, pi.add_apply, Lbar.mk_tensor_apply, finset.sum_congr,
    add_monoid_hom.smul_apply, pi.smul_apply, add_monoid_hom.finset_sum_apply, finset.smul_sum],
  rw [finset.sum_add_distrib, finset.sum_const, finset.card_univ,
    fintype.card_fin, finset.sum_comm, ← hx₀],
end

lemma lem98_crux [fact (r' < 1)] {ι : Type} {l : ι → Λ}
  (N : ℕ) (hN : 0 < N) (A : finset (Λ →+ ℤ))
  (x x₀ x₁ : Λ →+ Lbar r' S)
  (x' x₀' x₁' : S → ℕ → Λ →+ ℤ) [∀ s n a, decidable (x₁' s n = a)]
  (xₐ : (Λ →+ ℤ) → Lbar r' S)
  (hx : ∀ l s n, x l s n = x' s n l)
  (hx₀ : ∀ l s n, x₀ l s n = x₀' s n l)
  (hx₁ : ∀ l s n, x₁ l s n = x₁' s n l)
  (hxₐ : ∀ a, xₐ a = Lbar.mk_of_add_monoid_hom x₁' a)
  (Hx₁ : ∀ (l : Λ), x₁ l = ∑ (a : Λ →+ ℤ) in A, a l • xₐ a)
  (hx₁'A : ∀ s n, x₁' s n ∈ A)
  (H : ∀ s n i, (x' s n (l i)).nat_abs =
    N * (x₀' s n (l i)).nat_abs + (x₁' s n (l i)).nat_abs)
  (i : ι) :
  ∥x (l i)∥₊ = N • ∥x₀ (l i)∥₊ + ∑ a in A, ∥a (l i)∥₊ * ∥xₐ a∥₊ :=
begin
  simp only [hx, H, ← hx₀, ← hx₁, Lbar.nnnorm_def,
    nsmul_eq_mul, mul_assoc,
    finset.smul_sum, finset.mul_sum, nat.cast_add, nat.cast_mul, add_mul],
  rw [finset.sum_comm, ← finset.sum_add_distrib],
  apply fintype.sum_congr,
  intro s,
  apply nnreal.eq,
  simp only [nnreal.coe_tsum, nnreal.coe_sum, nnreal.coe_add, nnreal.coe_mul,
    nnreal.coe_pow, nnreal.coe_nat_cast, nnreal.coe_nat_abs, coe_nnnorm],
  rw [tsum_add _ ((x₁ (l i)).summable_coe_real s)], swap,
  { rw ← summable_mul_left_iff,
    { exact (x₀ (l i)).summable_coe_real s },
    { exact_mod_cast hN.ne' } },
  simp only [← tsum_mul_left],
  rw [← tsum_sum], swap,
  { intros a ha, exact summable.mul_left _ ((xₐ a).summable_coe_real s) },
  simp only [← mul_assoc, ← finset.sum_mul, hxₐ, Hx₁],
  congr, ext n, congr,
  simp only [finset.sum_apply, Lbar.coe_sum, Lbar.mk_of_add_monoid_hom_to_fun,
    pi.smul_apply],
  rw [finset.sum_eq_single (x₁' s n), finset.sum_eq_single (x₁' s n)],
  { simp only [Lbar.coe_zsmul, Lbar.mk_of_add_monoid_hom_to_fun, if_true,
      pi.smul_apply, eq_self_iff_true, true_and, if_congr, and_congr],
    split_ifs,
    { simp only [mul_zero, norm_zero, smul_eq_mul] },
    { simp only [int.norm_eq_abs, ← abs_mul, ← int.cast_mul, smul_eq_mul] } },
  all_goals { try { intro hsnA, exact (hsnA (hx₁'A s n)).elim } },
  all_goals { intros a haA hasn },
  { simp only [hasn.symm, Lbar.mk_of_add_monoid_hom_to_fun, norm_zero,
      mul_zero, if_congr, and_congr, eq_self_iff_true, if_false, false_and] },
  { simp only [hasn.symm, Lbar.coe_zsmul, pi.smul_apply, smul_eq_mul,
      Lbar.mk_of_add_monoid_hom_to_fun, mul_zero,
      if_congr, and_congr, eq_self_iff_true, if_false, false_and] },
end
.

namespace lem98

def ι (Λ : Type*) [polyhedral_lattice Λ] : Type :=
(polyhedral_lattice.polyhedral Λ).some

instance : fintype (ι Λ) := (polyhedral_lattice.polyhedral Λ).some_spec.some

variables (Λ)

def l : ι Λ → Λ := (polyhedral_lattice.polyhedral Λ).some_spec.some_spec.some

lemma hl : generates_norm (l Λ) :=
by convert (polyhedral_lattice.polyhedral Λ).some_spec.some_spec.some_spec.1

lemma hl' : ∀ i, l Λ i ≠ 0 :=
(polyhedral_lattice.polyhedral Λ).some_spec.some_spec.some_spec.2

def A (N : ℕ) [hN : fact (0 < N)] := (lem97' N hN.1 (l Λ)).some

lemma hA (N : ℕ) [hN : fact (0 < N)] (x : Λ →+ ℤ) :
  ∃ x' (H : x' ∈ A Λ N) y, x = N • y + x' ∧
    ∀ i, (x (l Λ i)).nat_abs = N * (y (l Λ i)).nat_abs + (x' (l Λ i)).nat_abs :=
(lem97' N hN.1 (l Λ)).some_spec x

def d  (N : ℕ) [hN : fact (0 < N)] : ℝ≥0 :=
finset.univ.sup (λ i, ∑ a in A Λ N, ∥a (l Λ i)∥₊ / ∥l Λ i∥₊)

end lem98

theorem lem98_finite [fact (r' < 1)] (Λ : Type*) [polyhedral_lattice Λ] (S : Type*) [fintype S]
  (N : ℕ) [hN : fact (0 < N)] :
  pseudo_normed_group.splittable (Λ →+ Lbar r' S) N (lem98.d Λ N) :=
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
.

#lint- only unused_arguments
