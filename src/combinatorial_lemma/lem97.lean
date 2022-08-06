import algebra.group.basic
import analysis.convex.cone
import linear_algebra.dual
import algebra.order.ring
import algebra.module.hom
import ring_theory.finiteness

import for_mathlib.Gordan

/-!

# Lemma 9.7 of [Analytic]

In this file we state and prove 9.7 of [Analytic]. The proof in the pdf is short, but
combinatorics can be fiddly. However it is almost certain that this file could be
a lot shorter.

-/

open_locale nnreal big_operators classical

variables {Λ : Type*} [add_comm_group Λ]
variable {ι : Type*}

noncomputable theory

open classical subtype function embedding

/-- A technical auxiliary lemma used in the proof of `lem97_pos`. -/
lemma aux_1 {N : ℕ} {l : ι → Λ} {S₀ : finset (Λ →+ ℤ)}
  (hS₀ : submodule.span ℕ ↑S₀ = explicit_dual_set l) :
  let ψ : ({x // x ∈ S₀} → fin N) → Λ →+ ℤ :=
        λ (y : {x // x ∈ S₀} → fin N), ∑ (s : {x // x ∈ S₀}) in S₀.attach, (y s).val • s.val,
      B : finset (Λ →+ ℤ) := finset.image ψ finset.univ
  in ∀ (b : Λ →+ ℤ), b ∈ B → b ∈ explicit_dual_set l :=
begin
  intros ψ B b hb,
  rcases finset.mem_image.mp hb with ⟨y, ⟨hy₁, rfl⟩⟩,
  rw [← hS₀],
  apply mem_span_finset.mpr,
  refine ⟨λ x : (Λ →+ ℤ), if H: x ∈ S₀ then (y ⟨x, H⟩ : ℕ) else 0, _⟩,
  rw ← finset.sum_attach,
  refine finset.sum_congr rfl (λ s hs, _),
  simp only [*, dif_pos, dite_eq_ite, val_eq_coe, if_true, finset.coe_mem, finset.mk_coe]
end

/-- A technical auxiliary lemma used in the proof of `lem97_pos`. -/
lemma aux_2 {N : ℕ} (hN : 0 < N) {l : ι → Λ} {S₀ : finset (Λ →+ ℤ)}
  (hS₀ : submodule.span ℕ ↑S₀ = explicit_dual_set l) {f r : (Λ →+ ℤ) → ℕ} :
  let Y : Type u_1 := {x // x ∈ S₀} → fin N,
      ψ : Y → Λ →+ ℤ := λ (y : Y), ∑ (s : {x // x ∈ S₀}) in S₀.attach, (y s).val • s.val,
      B : finset (Λ →+ ℤ) := finset.image ψ finset.univ,
      g : (Λ →+ ℤ) → fin N := λ (i : Λ →+ ℤ), ⟨f i % N, nat.mod_lt _ hN⟩,
      x' : Λ →+ ℤ := ∑ (i : Λ →+ ℤ) in S₀, (g i).val • i
  in f = ↑g + N • r → x' = ∑ (i : Λ →+ ℤ) in S₀, (g i).val • i → x' ∈ B →
    ∀ (i : ι), x' (l i) ≤ (⇑∑ (i : Λ →+ ℤ) in S₀, f i • i) (l i) :=
begin
  intros Y ψ B g x' hr hx' H i,
  dsimp [x'],
  rw [sub_nonpos.symm, sub_eq_add_neg, ← add_monoid_hom.neg_apply, ← finset.sum_neg_distrib,
    add_monoid_hom.finset_sum_apply, add_monoid_hom.finset_sum_apply, ← finset.sum_add_distrib],
  swap, apply_instance,
  simp only [← add_monoid_hom.add_apply, ← nsmul_eq_smul, ← coe_nat_zsmul, ← neg_zsmul,
     zsmul_eq_smul, ← add_smul],
  simp only [add_monoid_hom.add_apply, add_monoid_hom.smul_apply, pi.add_apply, pi.neg_apply,
     int.coe_nat_mod, pi.smul_apply, add_monoid_hom.neg_apply],
  apply finset.sum_nonpos,
  intros z hz,
  replace hz : z ∈ explicit_dual_set l,
  { rw [← submodule.span_singleton_le_iff_mem, ← hS₀],
    exact submodule.span_mono (set.singleton_subset_iff.mpr hz) },
  replace hz : 0 ≤ z (l i) := rfl.mpr hz i,
  simp only [- add_neg_le_iff_le_add', tactic.ring.add_neg_eq_sub, smul_sub],
  rw sub_smul,
  rw [← int.coe_nat_mod, sub_le_iff_le_add, zero_add],
  simp only [has_smul.smul, zsmul_int_int],
  exact (mul_le_mul_of_nonneg_right (int.coe_nat_le.mpr (nat.mod_le (f z) N)) hz),
end

/-- A technical auxiliary lemma used in the proof of `lem97_pos`. -/
lemma aux_3 {N : ℕ} (hN : 0 < N) {l : ι → Λ} {S₀ : finset (Λ →+ ℤ)}
  (hS₀ : submodule.span ℕ ↑S₀ = explicit_dual_set l) :
  let Y : Type u_1 := {x // x ∈ S₀} → fin N,
      ψ : Y → Λ →+ ℤ := λ (y : Y), ∑ (s : {x // x ∈ S₀}) in S₀.attach, (y s).val • s.val,
      B : finset (Λ →+ ℤ) := finset.image ψ finset.univ
  in ∀ (x : Λ →+ ℤ), x ∈ explicit_dual_set l → (∃ (x' : Λ →+ ℤ) (H : x' ∈ B) (y : Λ →+ ℤ),
      x = N • y + x' ∧ ∀ (i : ι), x' (l i) ≤ x (l i)) :=
begin
  intros Y ψ B x hx,
  rw [← hS₀, mem_span_finset] at hx,
  rcases hx with ⟨f, rfl⟩,
  let g : (Λ →+ ℤ) → (fin N) := (λ i, ⟨f i % N, nat.mod_lt (f i) hN⟩),
  obtain ⟨r, hr⟩ : ∃ (r : (Λ →+ ℤ) → ℕ), f = ↑g + N • r,
  { use λ x, (f x - g x) / N,
    refine funext (λ z, (_ : f z = g z + N * ((f z - f z % N) / N))),
    rw [nat.mul_div_cancel' (nat.dvd_sub_mod _)],
    exact (add_tsub_cancel_of_le (nat.mod_le _ _)).symm },
  set x' := ∑ (i : Λ →+ ℤ) in S₀, (g i).val • i with hx',
  have H : x' ∈ B,
  { refine finset.mem_image.mpr ⟨g ∘ val, finset.mem_univ _, _⟩,
    convert finset.sum_attach,
    refl },
  refine ⟨x', _, ∑ (i : Λ →+ ℤ) in S₀, r i • i, _, _⟩,
  { refine finset.mem_image.mpr ⟨g ∘ val, finset.mem_univ _, _⟩,
    convert finset.sum_attach,
    refl },
  { rw [hr, finset.smul_sum, ← finset.sum_add_distrib],
    simp_rw [← smul_assoc, ← add_smul, add_comm (N • _) _],
    refl },
  exact aux_2 hN hS₀ hr hx' H,
end

/-- The proof of Lemma 9.7 of `Analytic.pdf` under the additional assumption
that (in the notation of the paper) λᵢ(x)≥0 for all i. -/
lemma lem97_pos [module.finite ℤ Λ] [module.free ℤ Λ] [fintype ι] (N : ℕ) (hN : 0 < N) (l : ι → Λ) :
  ∃ B : finset (Λ →+ ℤ), (∀ b ∈ B, b ∈ (explicit_dual_set l)) ∧
    ∀ x : Λ →+ ℤ, x ∈ (explicit_dual_set l) → ∃ (x' ∈ B) (y : Λ →+ ℤ),
    x = N • y + x' ∧ ∀ i, x' (l i) ≤ x (l i) :=
begin
  obtain ⟨S₀, hS₀⟩ := explicit_gordan l,
  let Y : Type* := { x // x ∈ S₀ } → (fin N),
  let ψ : Y → Λ →+ ℤ := λ y : Y, ∑ s in finset.attach S₀, (y s).1 • s.val,
  exact ⟨finset.image ψ finset.univ, aux_1 hS₀, aux_3 hN hS₀⟩,
end

section sign_vectors

def nonzero_sign : ℤ → units ℤ := λ n, if 0 ≤ n then 1 else -1

def sign_vectors (ι : Type*) := (ι → units ℤ)

instance sign_vectors_inhabited : inhabited (sign_vectors ι) := ⟨(λ i, 1)⟩

def fintype_sign_vectors [fintype ι] : fintype (sign_vectors ι) := pi.fintype

/-- Given a list l of elements of Λ and a functional x, (pos_vector l x) is the sign-vector of
the values of x (l i). -/
def pos_vector (l : ι → Λ) (x : Λ →+ ℤ) : sign_vectors ι :=
λ i, nonzero_sign (x (l i))

instance smul_signs : has_smul (sign_vectors ι) (ι → Λ) :=
{ smul := λ ε l i, (ε i : ℤ) • l i }

lemma pos_vector_nonneg (l : ι → Λ) (x : Λ →+ ℤ) (j : ι) :
  0 ≤ x ((pos_vector l x • l) j) :=
begin
  rw [pos_vector, nonzero_sign],
  simp only [has_smul.smul, add_monoid_hom.map_zsmul, zsmul_int_int],
  split_ifs,
  { convert h, simp },
  { simp, linarith }
end

lemma smul_to_explicit_dual_set (l : ι → Λ) (x : Λ →+ ℤ) :
  x ∈ (explicit_dual_set ((pos_vector l x) • l)) :=
λ j, pos_vector_nonneg l x j

lemma pos_vector_id_if_nonneg (l : ι → Λ) (x : Λ →+ ℤ) (i : ι) : 0 ≤ x (l i) →
    (pos_vector l x • l) i = l i :=
begin
  intro hx,
  simp only [pos_vector, nonzero_sign, has_smul.smul, id.def],
  rw [if_pos hx],-- units.coe_one, one_zsmul],
  simp,
end

lemma pos_vector_neg_if_neg (l : ι → Λ) (x : Λ →+ ℤ) (i : ι) : x (l i) < 0 →
    ((pos_vector l x) • l) i = - l i :=
begin
  intro hx,
  simp only [pos_vector, nonzero_sign, has_smul.smul, id.def],
  rw [if_neg (not_le.mpr hx)], simp,
end


end sign_vectors

/-- Given a list l, a vector of signs ε (and a positive integer N), (pos_A l ε) is a finite set of
functionals satisfying the requirements of Lemma 9.7 of [Analytic] with respect to all functionals
which are positive on all ((ε • l) i)'s. Its existence was established in lem97_pos above.
-/
def pos_A [fintype ι] [module.finite ℤ Λ] [module.free ℤ Λ] (N : ℕ) (hN : 0 < N)
  (l : ι → Λ) (ε : sign_vectors ι) : finset (Λ →+ ℤ) :=
some (lem97_pos N hN (ε • l))

lemma posA_to_explicit [fintype ι] [module.finite ℤ Λ] [module.free ℤ Λ]
  (N : ℕ) (hN : 0 < N) (l : ι → Λ) (ε : sign_vectors ι) (x' : Λ →+ ℤ) (H : x' ∈ pos_A N hN l ε) :
  x' ∈ explicit_dual_set (ε • l) :=
(some_spec (lem97_pos N hN (ε • l))).1 x' H


lemma exists_good_pair [fintype ι] [module.finite ℤ Λ] [module.free ℤ Λ]
  (N : ℕ) (hN : 0 < N) (l : ι → Λ)
  (ε : sign_vectors ι) (x : Λ →+ ℤ) (H : x ∈ (explicit_dual_set (ε • l))) :
  ∃ x' y : (Λ →+ ℤ),
    x' ∈ pos_A N hN l ε ∧ x = N • y + x' ∧ ∀ i, x' ((ε • l) i) ≤ x ((ε • l) i) :=
begin
  obtain ⟨x', hx', ⟨y, hy⟩⟩ := (some_spec (lem97_pos N hN (ε • l))).2 x H,
  exact ⟨x', y, hx', hy⟩,
end

/-

The remainder of this file is proofs of two versions of Lemma 9.7, namely
`lem97` and `lem97'`.

-/


/-- Lemma 9.7 of [Analytic]. See also the (mathematically indistinguishable) variant `lem97'`. -/
lemma lem97 [fintype ι] [module.finite ℤ Λ] [module.free ℤ Λ] (N : ℕ) (hN : 0 < N) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (0 ≤ x' (l i) ∧ 0 ≤ (x - x') (l i)) ∨ (x' (l i) ≤ 0 ∧ (x - x') (l i) ≤ 0) :=
begin
  refine ⟨(@finset.univ (sign_vectors ι) (fintype_sign_vectors)).bUnion (pos_A N hN l), λ x, _⟩,
  have hx : x ∈ (explicit_dual_set ((pos_vector l x) • l)) := smul_to_explicit_dual_set l x,
  obtain ⟨x', y, mem_x', hy, hx'⟩ := exists_good_pair N hN l (pos_vector l x) x hx,
  refine ⟨x', _, _⟩,
  { refine finset.mem_bUnion.mpr ⟨pos_vector l x, _, mem_x'⟩,
    simp only [finset.mem_univ] },
  { refine ⟨y, hy, λ i, _⟩,
    have h_pos' : x' ∈ explicit_dual_set ((pos_vector l x) • l) :=
      posA_to_explicit N hN l (pos_vector l x) x' mem_x',
    replace h_pos' : 0 ≤ x' (((pos_vector l x) • l) i) := h_pos' _,
    by_cases h_pos : 0 ≤ x (l i),
    { have h_posvect_id : ((pos_vector l x) • l) i = l i := pos_vector_id_if_nonneg l x i h_pos,
      replace h_pos' : 0 ≤ x' (l i) := h_pos'.trans (le_of_eq (congr_arg x' h_posvect_id)),
      refine or.inl ⟨h_pos', _⟩,
      rw ← h_posvect_id,
      simp only [sub_nonneg, add_monoid_hom.sub_apply, hx'] },
    { specialize hx' i,
      have h_posvect_neg : ((pos_vector l x) • l) i = - l i :=
        pos_vector_neg_if_neg l x i (not_le.mp h_pos),
      rw [h_posvect_neg] at *,
      replace h_pos' : x' (l i) ≤ 0,
      { rw [x'.map_neg] at h_pos',
        exact neg_nonneg.mp h_pos' },
      refine or.inr ⟨h_pos', _⟩,
      simpa only [neg_le_neg_iff, add_monoid_hom.sub_apply, add_monoid_hom.map_neg, sub_nonpos]
        using hx' } }
end

lemma os.monotone_pow {R : Type*} [ordered_semiring R] (k : ℕ) (R0 : ∀ r : R, 0 ≤ r) :
  monotone (λ n : R, n ^ k) :=
λ x y xy, pow_le_pow_of_le_left (R0 _) xy k

lemma nat.monotone_pow (k : ℕ) : monotone (λ n : ℕ, n ^ k) :=
os.monotone_pow k nat.zero_le
--λ x y xy, pow_le_pow_of_le_left x.zero_le xy k

lemma nat.strict_mono_pow {k : ℕ} (k0 : 0 < k) : strict_mono (λ n : ℕ, n ^ k) :=
λ x y xy, pow_lt_pow_of_lt_left xy x.zero_le k0

lemma nat.injective_pow {k : ℕ} (k0 : 0 < k) : function.injective (λ n : ℕ, n ^ k) :=
injective_of_increasing (<) (<) _ (nat.strict_mono_pow k0)

lemma int.nat_abs_eq_self (a : ℤ) : (a.nat_abs : ℤ) = a ↔ 0 ≤ a :=
⟨λ h, by { rw ← h, exact int.coe_zero_le a.nat_abs }, λ h, int.nat_abs_of_nonneg h⟩

lemma abs_add_eq_iff_abs_mul_eq {R : Type*} [linear_ordered_comm_ring R] {a b : R} :
  abs (a + b) = abs a + abs b ↔ abs (a * b) = a * b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { simpa only [abs_mul, add_pow_two, mul_assoc, pow_bit0_abs, add_left_inj, mul_eq_mul_left_iff,
      or_false, bit0_eq_zero, one_ne_zero, add_right_inj] using congr_arg (λ x : R, x ^ 2) h.symm },
  { rcases (mul_nonneg_iff.mp (abs_eq_self.mp h)) with ⟨a0, b0⟩ | ⟨a0, b0⟩,
    { rw [abs_of_nonneg a0, abs_of_nonneg b0, abs_of_nonneg (add_nonneg a0 b0)] },
    { rw [abs_of_nonpos a0, abs_of_nonpos b0, abs_of_nonpos (add_nonpos a0 b0), neg_add] } }
end

lemma nat_abs_add_eq_iff_nat_abs_mul_eq {a b : ℤ} :
  int.nat_abs (a + b) = a.nat_abs + b.nat_abs ↔ ((a * b).nat_abs : ℤ) = a * b :=
begin
  rw [← int.abs_eq_nat_abs, ← abs_add_eq_iff_abs_mul_eq, int.abs_eq_nat_abs, int.abs_eq_nat_abs,
    int.abs_eq_nat_abs],
  norm_cast,
end

lemma nat_abs_add_eq_iff (a b : ℤ) :
  int.nat_abs (a + b) = int.nat_abs a + int.nat_abs b ↔ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) :=
nat_abs_add_eq_iff_nat_abs_mul_eq.trans ((int.nat_abs_eq_self _).trans mul_nonneg_iff)

lemma nat_smul_nat_abs (a : ℕ) (b : ℤ) : a • b.nat_abs = (a • b).nat_abs :=
begin
  nth_rewrite 0 [← int.nat_abs_of_nat a],
  rw [smul_eq_mul, ← int.nat_abs_mul, ← smul_eq_mul],
  apply congr_arg,
  rw [algebra.id.smul_eq_mul, nsmul_eq_mul],
end

/-- Lemma 9.7 of [Analytic]. See also the (mathematically indistinguishable) variant `lem97`. -/
lemma lem97' [fintype ι] [module.finite ℤ Λ] [module.free ℤ Λ] (N : ℕ) (hN : 0 < N) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (x (l i)).nat_abs = N * (y (l i)).nat_abs + (x' (l i)).nat_abs :=
begin
  obtain ⟨A, hA⟩ := lem97 N hN l,
  refine ⟨A, λ x, _⟩,
  rcases hA x with ⟨x', mem_x', y, rfl, hx'⟩,
  refine ⟨x', mem_x', y, rfl, λ i, _⟩,
  specialize hx' i,
  rw [← nat_abs_add_eq_iff, add_sub_cancel, add_monoid_hom.coe_smul, pi.smul_apply] at hx',
  rw [add_monoid_hom.add_apply, add_monoid_hom.coe_smul, pi.smul_apply, add_comm, hx', add_comm,
    add_left_inj, ← nat_smul_nat_abs, smul_eq_mul],
end

-- TODO
-- #lint-

-- /- The `doc_blame` linter reports: -/
-- /- DEFINITIONS ARE MISSING DOCUMENTATION STRINGS: -/
-- #print nonzero_sign /- def missing doc string -/
-- #print sign_vectors /- def missing doc string -/
-- #print fintype_sign_vectors /- def missing doc string -/
