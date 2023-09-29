import thm95.constants
import breen_deligne.eg

open_locale nnreal

variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]

/-
Goal: show that `k κ' m`, and `K r r' BD κ' m` grow doubly exponential in `m`.
-/

namespace thm95
namespace universal_constants

open system_of_double_complexes

section eg

open breen_deligne.eg

@[simp] lemma eg_factor_hom (n : ℕ) :
  breen_deligne.universal_map.factor (breen_deligne.eg.homotopy.hom n (n + 1)) = 1 :=
begin
  dsimp only [breen_deligne.eg, h],
  rw [dif_pos rfl],
  dsimp [hmap, breen_deligne.universal_map.factor],
  refine (finset.sup_congr rfl _).trans (finset.sup_const _ _),
  { rintro ⟨f, i⟩ hf,
    simp only [finset.mem_product, finset.mem_univ, and_true] at hf,
    erw [free_abelian_group.support_of, finset.mem_singleton] at hf, subst hf,
    dsimp,
    let i' : fin (2 * BD.X n) := i,
    rw finset.sum_eq_single i',
    { norm_cast,
      simp only [breen_deligne.basic_universal_map.id, matrix.one_apply_eq, int.nat_abs_one] },
    { rintro j - hj,
      norm_cast,
      rwa [breen_deligne.basic_universal_map.id, matrix.one_apply_ne', int.nat_abs_zero], },
    { intro h, exact (h $ finset.mem_univ _).elim } },
  { refine ⟨⟨_, ⟨0, pow_pos zero_lt_two (n+1)⟩⟩, _⟩, swap,
    simp only [finset.mem_product, finset.mem_univ, and_true],
    erw [free_abelian_group.support_of, finset.mem_singleton], }
end

@[simp] lemma factor_proj (N n : ℕ) : (breen_deligne.universal_map.proj n N).factor = 1 :=
begin
  refine (finset.sup_congr rfl _).trans (finset.sup_const _ _),
  { rintro ⟨f, i⟩ hf,
    obtain ⟨k, rfl⟩ : ∃ k, f = breen_deligne.basic_universal_map.proj n k,
    sorry { simp only [finset.mem_product, finset.mem_univ, and_true] at hf,
      dsimp only [breen_deligne.universal_map.proj] at hf,
      have := free_abelian_group.support_sum (finset.univ : finset (fin N)) (λ _, 1),
      squeeze_simp at this,
      rw [free_abelian_group.sum_support_coeff] at hf, sorry },
    clear hf,
    rw [finset.sum_eq_single (fin_prod_fin_equiv (k, i))],
    sorry { dsimp only [breen_deligne.basic_universal_map.proj,
        breen_deligne.basic_universal_map.proj_aux],
      simp only [matrix.reindex_linear_equiv_apply, matrix.reindex_apply, matrix.submatrix_apply,
        equiv.punit_prod_symm_apply, matrix.kronecker_apply, boole_mul, nat.cast_eq_one, one_mul,
        equiv.symm_apply_apply, eq_self_iff_true, matrix.one_apply_eq, if_true, int.nat_abs_one], },
    { refine fin_prod_fin_equiv.forall_congr_left.mp _,
      rintro ⟨l, j⟩ - hlj,
      dsimp only [breen_deligne.basic_universal_map.proj,
        breen_deligne.basic_universal_map.proj_aux],
      simp only [matrix.reindex_linear_equiv_apply, matrix.reindex_apply, matrix.submatrix_apply,
        equiv.punit_prod_symm_apply, matrix.kronecker_apply, boole_mul, nat.cast_eq_one, one_mul,
        equiv.symm_apply_apply, eq_self_iff_true, matrix.one_apply_eq, if_true, int.nat_abs_one],
      sorry },
    { intro h, exact (h $ finset.mem_univ _).elim } },
  { sorry }
end

@[simp] lemma factor_sum (N n : ℕ) : (breen_deligne.universal_map.sum n N).factor = 1 :=
begin
  dsimp only [breen_deligne.universal_map.sum],
  sorry
end

@[simp] lemma eg_factor_d (n : ℕ) :
  breen_deligne.universal_map.factor (breen_deligne.eg.data.d (n + 1) n) ≤ 1 :=
begin
  dsimp only [breen_deligne.eg, BD],
  rw [dif_pos rfl],
  dsimp only,
  induction n with n ih,
  { dsimp only [map, σπ],
    refine le_trans (breen_deligne.universal_map.factor_sub _ _) _,
    erw [factor_proj, factor_sum],
    simp only [max_eq_right], },
  dsimp only [map, σπ],
  sorry
end

@[simp] lemma eg_bound_d (n : ℕ) :
  breen_deligne.universal_map.bound (breen_deligne.eg.data.d (n + 1) n) = 3 ^ (n+1) :=
begin
  dsimp only [breen_deligne.eg, BD],
  rw [dif_pos rfl],
  induction n with n ih,
  { dsimp only [map, σπ],
    sorry },
  dsimp only [map, σπ],
  sorry
end

lemma eg_κ'_le_one [fact (r < 1)] (n : ℕ) :
  κ' r r' n ≤ 1 :=
begin
  induction n with n ih,
  { exact le_rfl },
  dsimp only [κ, κ', breen_deligne.data.κ, breen_deligne.package.κ'],
  simp only [eg_factor_hom, one_mul, mul_inv_rev, inv_inv, rescale_constants, ← mul_assoc],
  rw [mul_right_comm (breen_deligne.eg.data.κ r r' n), mul_inv_cancel, one_mul],
  swap, { apply ne_of_gt, apply fact.out },
  sorry -- AAAAHRG!! This is ae not true
end

end eg

variables (BD : breen_deligne.package) (κ : ℕ → ℝ≥0) [BD.data.very_suitable r r' κ]
variables (m : ℕ)
variables [∀ n, fact (BD.κ' κ n ≤ 1)] -- AAAAHRG!! This is ae not true

instance finset_sup_le_one [∀ n, fact (κ n ≤ 1)] (s : finset ℕ) : fact (s.sup κ ≤ 1) :=
begin
  constructor,
  apply finset.sup_le,
  intros,
  exact fact.out _
end

@[simp]
lemma max_eq_left' (a b : ℝ≥0) [ha : fact (1 ≤ a)] [hb : fact (b ≤ 1)] : max a b = a :=
max_eq_left $ hb.out.trans ha.out

lemma doubly_exponential_normed_spectral_k₀ (k : ℝ≥0) : normed_spectral.k₀ m k ≤ k ^ 3 ^ m :=
begin
  induction m with m ih generalizing k,
  { show k ≤ _, norm_num, },
  simp only [normed_spectral.k₀, pow_succ, pow_mul, pow_zero, mul_one, ← mul_assoc],
  exact ih _,
end

def triangle : ℕ → ℕ
| 0 := 0
| (m+1) := triangle m + m + 1

lemma doubly_exponential_k₁ : k₁ (BD.κ' κ) m ≤ 2 ^ 3 ^ (triangle m) :=
begin
  induction m with m ih,
  { show (2 : ℝ≥0) ≤ _, dsimp only [triangle], norm_num, },
  dsimp only [k₁],
  simp only [max_eq_left'],
  apply max_le,
  { conv_lhs { rw [← pow_one (2:ℝ≥0)] },
    refine pow_le_pow one_le_two _,
    exact nat.one_le_pow _ _ zero_lt_three, },
  { calc normed_spectral.k₀ m (k₁ (BD.κ' κ) m) ^ 2
        ≤ _ : pow_le_pow_of_le_left' (doubly_exponential_normed_spectral_k₀ _ _) 2
    ... ≤ _ : _,
    rw [← pow_mul],
    refine le_trans (pow_le_pow_of_le_left' ih _) _,
    rw [← pow_mul],
    refine pow_le_pow one_le_two _,
    simp only [triangle, pow_add, pow_one, ← mul_assoc],
    refine mul_le_mul' le_rfl _,
    norm_num, }
end

lemma doubly_exponential_k₀ : k₀ (BD.κ' κ) m ≤ 2 ^ 3 ^ (triangle m + m) :=
begin
  calc k₀ (BD.κ' κ) m
      ≤ k₁ (BD.κ' κ) m ^ 3 ^ m       : doubly_exponential_normed_spectral_k₀ _ _
  ... ≤ (2 ^ 3 ^ triangle m) ^ 3 ^ m : pow_le_pow_of_le_left' (doubly_exponential_k₁ _ _ _) _
  ... ≤ _ : _,
  rw [← pow_mul, ← pow_add],
end

lemma doubly_exponential_k : k (BD.κ' κ) m ≤ 4 ^ 3 ^ (triangle m + m) :=
begin
  delta k k',
  simp only [max_eq_left'],
  calc k₀ (BD.κ' κ) m * k₀ (BD.κ' κ) m
      ≤ (2 ^ 3 ^ (triangle m + m)) * (2 ^ 3 ^ (triangle m + m)) : mul_le_mul'
                                    (doubly_exponential_k₀ _ _ _) (doubly_exponential_k₀ _ _ _)
  ... ≤ 4 ^ 3 ^ (triangle m + m) : _,
  rw [← pow_two, ← pow_mul, pow_mul'],
  norm_num,
end

lemma doubly_exponential_K : K r r' BD (BD.κ' κ) m ≤ 2 ^ 2 ^ m :=
begin
  -- TODO: figure out the correct bases for the exponentials
  -- they better depend on `r`, `r'` and `κ'`
  sorry
end

end universal_constants
end thm95
