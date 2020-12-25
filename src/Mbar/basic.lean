import ring_theory.power_series
import data.real.basic
import algebra.big_operators.basic
import topology.algebra.infinite_sum
import data.finset.basic
import data.equiv.basic
import analysis.normed_space.basic
import analysis.specific_limits
import data.equiv.basic

import Mbar.bounded
/-!

## $\overline{\mathcal{M}}_{r'}(S)$

This file contains a definition of ℳ-barᵣ'(S) as defined on p57 of Analytic.pdf .
Currently it's a subtype.

## Implementation issues

We model Tℤ[[T]] as functions ℕ → ℤ which vanish at 0.

-/

universe u

noncomputable theory
open_locale big_operators

open power_series

/-- `Mbar r' S c` is the set of power series
`F_s = ∑ a_{n,s}T^n ∈ Tℤ[[T]]` such that `∑_{n,s} |a_{n,s}|r'^n ≤ c` -/
def Mbar (r' : ℝ) (S : Type u) [fintype S] (c : ℝ) :=
{F : S → ℕ → ℤ // (∀ s, F s 0 = 0) ∧
  (∀ s, summable (λ n, abs ((F s n : ℝ) * r'^n))) ∧
  (∑ s, ∑' n, (abs ((F s n : ℝ) * r'^n))) ≤ c }

variables {r' : ℝ} {S : Type u} [fintype S] {c c₁ c₂ : ℝ}

protected lemma Mbar.constant_coeff_eq_zero (x : Mbar r' S c) (s : S) : x.1 s 0 = 0 := x.2.1 s

protected lemma Mbar.summable (x : Mbar r' S c) (s : S) :
  summable (λ n, abs ((x.1 s n : ℝ) * r'^n)) := x.2.2.1 s

protected lemma Mbar.sum_tsum_le (x : Mbar r' S c) :
  (∑ s, ∑' n, (abs ((x.1 s n : ℝ) * r'^n))) ≤ c := x.2.2.2

protected def Mbar.cast_le (h : c₁ ≤ c₂) (x : Mbar r' S c₁) : Mbar r' S c₂ :=
⟨x.1, x.constant_coeff_eq_zero, x.summable, x.sum_tsum_le.trans h⟩

-- lemma abs_mul_pow_pos {x r : ℝ} (hr : 0 < r) {n : ℕ} :
--   abs (x * r ^ n) = abs x * r ^ n :=
-- by rw [abs_mul, abs_of_pos (pow_pos hr _)]

noncomputable def Mbar.add :
  Mbar r' S c₁ → Mbar r' S c₂ → Mbar r' S (c₁ + c₂) :=
λ F G, ⟨F.1 + G.1, begin
  rcases F with ⟨F, hF0, hFs, hFsc⟩,
  rcases G with ⟨G, hG0, hGs, hGsc⟩,
  have hFGs : ∀ (s : S), summable (λ (n : ℕ), abs (((F + G) s n : ℝ) * r' ^ n)),
  { intro s,
    simp_rw summable_abs_iff at hFs hGs ⊢,
    convert summable.add (hFs s) (hGs s),
    ext n,
    simp [add_mul] },
  refine ⟨λ s, by simp [hF0 s, hG0 s], hFGs, _⟩,
  refine le_trans _ (add_le_add hFsc hGsc),
  rw ← finset.sum_add_distrib,
  refine finset.sum_le_sum _,
  rintro s -,
  rw ← tsum_add (hFs s) (hGs s),
  refine tsum_le_tsum _ (hFGs s) (summable.add (hFs s) (hGs s)),
  intro n,
  convert abs_add _ _,
  simp [add_mul],
end⟩

def Mbar.add' : Mbar r' S c₁ × Mbar r' S c₂ → Mbar r' S (c₁ + c₂) := λ x, Mbar.add x.1 x.2

lemma sum_fin_eq {M : ℕ} (f : ℕ → ℝ) : ∑ i in finset.range M, f i = ∑ (i : fin M), f i :=
@finset.sum_bij' ℕ ℝ (fin M) _ (finset.range M) finset.univ f (λ i, f i)
  (λ a ha, ⟨a, finset.mem_range.mp ha⟩) (λ a ha, finset.mem_univ _) (λ a ha, rfl)
  (λ a _, a) (λ a ha, finset.mem_range.mpr a.2) (λ a ha, rfl) (λ a ha, by simp)

def Tinv_aux {R : Type*} [has_zero R] : (ℕ → R) → ℕ → R := λ F n, if n = 0 then 0 else F (n + 1)

@[simp] lemma Tinv_aux_zero {R : Type*} [has_zero R] (f : ℕ → R) : Tinv_aux f 0 = 0 := rfl

@[simp] lemma Tinv_aux_succ {R : Type*} [has_zero R] (f : ℕ → R) (i : ℕ) :
  Tinv_aux f (i + 1) = f (i + 2) :=
if_neg (nat.succ_ne_zero i)

namespace Mbar

/-- The truncation map fro Mbar to Mbar_bdd -/
def truncate (M : ℕ) : Mbar r' S c → Mbar_bdd r' ⟨S⟩ c M := λ F,
⟨λ s n, F.1 s n.1, begin
  rcases F with ⟨F,hF1,hF2,hF3⟩,
  refine ⟨λ s, by simpa using hF1 s, le_trans _ hF3⟩,
  apply finset.sum_le_sum,
  rintros (s : S) -,
  simp only [fin.val_eq_coe],
  rw ← sum_fin_eq (λ i, abs ((F s i : ℝ) * r' ^i)),
  exact sum_le_tsum _ (λ _ _, abs_nonneg _) (hF2 s),
end⟩

-- /-- The truncation maps commute with the transition maps. -/
-- lemma truncate_transition {hr : 0 < r'} {M N : ℕ} (h : M ≤ N) (x : Mbar r' S c) :
--   transition h (truncate hr N x) = truncate hr M x := by tidy

-- Injectivity of the map Mbar to limit of Mbar_bdd
lemma eq_iff_truncate_eq (x y : Mbar r' S c)
  (cond : ∀ M, truncate M x = truncate M y) : x = y :=
begin
  ext s n,
  change (truncate n x).1 s ⟨n, by linarith⟩ = (truncate n y).1 s ⟨n,_⟩,
  rw cond,
end

/-- Underlying function of the element of Mbar f' S associated to a sequence of
  elements of the truncated Mbars. -/
def mk_seq (T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M) : S → ℕ → ℤ :=
  λ s n, (T n).1 s ⟨n, by linarith⟩

lemma mk_seq_zero {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M} (s : S) : mk_seq T s 0 = 0 := (T 0).2.1 s

lemma mk_seq_eq_of_compat {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M)
  {s : S} {n : ℕ} {M : ℕ} (hnM : n < M + 1) :
  mk_seq T s n = (T M).1 s ⟨n, hnM⟩ :=
begin
  have hnM : n ≤ M := nat.lt_succ_iff.mp hnM,
  unfold mk_seq,
  rw ← compat n M hnM,
  apply Mbar_bdd.transition_eq,
end

lemma mk_seq_sum_range_eq (T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M)
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) (s : S) (n) :
  ∑ i in finset.range (n+1), abs ((mk_seq T s i : ℝ) * r'^i) =
  ∑ i : fin (n+1), abs (((T n).1 s i : ℝ) * r'^i.1) :=
begin
  rw sum_fin_eq,
  congr',
  ext ⟨i, hi⟩,
  congr',
  exact mk_seq_eq_of_compat compat _,
end

lemma mk_seq_summable {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) (s : S) :
  summable (λ (n : ℕ), abs (↑(mk_seq T s n) * r' ^ n)) :=
begin
  refine @summable_of_sum_range_le (λ n, abs ((mk_seq T s n : ℝ) * r'^n)) c
    (λ _, abs_nonneg _) (λ n, _),
  cases n,
  { exact le_trans (by simp) (Mbar_bdd.nonneg_of_Mbar_bdd (T 0)) },
  { rw mk_seq_sum_range_eq T compat s n,
    refine le_trans _ (T n).2.2,
    refine finset.single_le_sum (λ _ _, _) (finset.mem_univ s),
    exact finset.sum_nonneg (λ _ _, abs_nonneg _) },
end

open filter

lemma mk_seq_tendsto {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) :
  tendsto (λ (n : ℕ), ∑ (s : S), ∑  i in finset.range n, abs ((mk_seq T s i : ℝ) * r'^i))
  at_top (nhds $ ∑ (s : S), ∑' n, abs ((mk_seq T s n : ℝ) * r'^n)) := tendsto_finset_sum _ $
λ s _, has_sum.tendsto_sum_nat $ summable.has_sum $ mk_seq_summable compat s

lemma mk_seq_sum_le {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) :
  (∑ s, ∑' (n : ℕ), abs (↑(mk_seq T s n) * r' ^ n)) ≤ c :=
begin
  refine le_of_tendsto (mk_seq_tendsto compat) (eventually_of_forall _),
  rintros (_ | n),
  { simp [Mbar_bdd.nonneg_of_Mbar_bdd (T 0)] },
  { convert (T n).2.2,
    funext,
    rw mk_seq_sum_range_eq T compat s n,
    refl }
end

lemma truncate_mk_seq {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) (M : ℕ) :
  truncate M ⟨mk_seq T, mk_seq_zero, mk_seq_summable compat, mk_seq_sum_le compat⟩ = T M :=
begin
  ext s ⟨i, hi⟩,
  exact mk_seq_eq_of_compat compat _,
end

/-
-- Surjectivity
lemma of_compat (T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M)
  (compat : ∀ (M N : ℕ) (h : M ≤ N), transition r' h (T N) = T M) :
  ∃ (F : Mbar r' S c), ∀ M, truncate M F = T M :=
⟨⟨mk_seq T, mk_seq_zero, mk_seq_summable compat, mk_seq_sum_le compat⟩, truncate_mk_seq compat⟩
-/

def of_compat {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) : Mbar r' S c :=
⟨mk_seq T, mk_seq_zero, mk_seq_summable compat, mk_seq_sum_le compat⟩

@[simp] lemma truncate_of_compat {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) (M : ℕ) :
  truncate M (of_compat compat) = T M :=
begin
  ext s ⟨i, hi⟩,
  exact mk_seq_eq_of_compat compat _,
end

def eqv : Mbar r' S c ≃ Mbar_bdd.limit r' ⟨S⟩ c :=
{ to_fun := λ F, ⟨λ N, truncate _ F, by tidy⟩,
  inv_fun := λ F, of_compat F.2,
  left_inv := by tidy,
  right_inv := by tidy }


section topological_structure

instance : topological_space (Mbar r' S c) := topological_space.induced eqv (by apply_instance)

lemma is_open_iff {U : set (Mbar_bdd.limit r' ⟨S⟩ c)} : is_open (eqv ⁻¹' U) ↔ is_open U :=
begin
  -- this should be made cleaner with some mathlib lemmas
  -- about images/preimages of sets under equiv's.
  rw is_open_induced_iff,
  split,
  { rintros ⟨V,hV,h⟩,
    apply_fun (λ S, eqv '' S) at h,
    simp_rw [eqv.image_eq_preimage] at h,
    have : V = U, { convert h, by tidy, by tidy },
    rw ← this,
    assumption },
  { intros hU,
    exact ⟨U,hU,rfl⟩ },
end

def homeo : Mbar r' S c ≃ₜ Mbar_bdd.limit r' ⟨S⟩ c :=
{ continuous_to_fun := begin
    simp only [equiv.to_fun_as_coe, continuous_def],
    intros U hU,
    rwa is_open_iff
  end,
  continuous_inv_fun := begin
    simp only [equiv.to_fun_as_coe, continuous_def],
    intros U hU,
    erw [← eqv.image_eq_preimage, ← is_open_iff],
    have : eqv ⁻¹' (eqv '' U) = U, by tidy, -- this should be in mathlib.
    rwa this,
  end,
  ..eqv }

lemma truncate_eq (M : ℕ) : (truncate M : Mbar r' S c → Mbar_bdd r' ⟨S⟩ c M) =
  (Mbar_bdd.proj M) ∘ homeo := rfl

instance : t2_space (Mbar r' S c) :=
⟨λ x y h, separated_by_continuous homeo.continuous (λ c, h $ homeo.injective c)⟩

instance [fact (0 < r')] : compact_space (Mbar r' S c) :=
begin
  constructor,
  rw homeo.embedding.compact_iff_compact_image,
  simp only [set.image_univ, homeomorph.range_coe],
  obtain ⟨h⟩ := (by apply_instance : compact_space (Mbar_bdd.limit r' ⟨S⟩ c)),
  exact h,
end

instance : totally_disconnected_space (Mbar r' S c) :=
begin
  constructor,
  intros A _ hA,
  constructor,
  suffices subsing : subsingleton (homeo '' A),
  { -- This block can probably be streamlined a bit...
    rintros ⟨a,ha⟩ ⟨b,hb⟩,
    ext1,
    suffices : homeo a = homeo b, by exact homeo.injective this,
    let x : ↥(homeo '' A) := ⟨homeo a, ⟨a, ha, rfl⟩⟩,
    let y : ↥(homeo '' A) := ⟨homeo b, ⟨b, hb, rfl⟩⟩,
    cases subsing,
    change ↑x = ↑y,
    rw subsing x y },
  obtain ⟨h⟩ := (by apply_instance : totally_disconnected_space (Mbar_bdd.limit r' ⟨S⟩ c)),
  exact h _ (by tauto) (is_preconnected.image hA _ homeo.continuous.continuous_on),
end

lemma continuous_iff {α : Type*} [topological_space α] (f : α → Mbar r' S c) :
  continuous f ↔ (∀ M, continuous ((truncate M) ∘ f)) :=
begin
  split,
  { intros hf M,
    rw [truncate_eq, function.comp.assoc],
    revert M,
    rw ← Mbar_bdd.continuous_iff,
    refine continuous.comp homeo.continuous hf },
  { intro h,
    suffices : continuous (homeo ∘ f), by rwa homeo.comp_continuous_iff at this,
    rw Mbar_bdd.continuous_iff,
    exact h }
end

lemma continuous_truncate {M} : continuous (@truncate r' S _ c M) := (continuous_iff id).mp continuous_id _

lemma continuous_add' : continuous (Mbar.add' : _ → Mbar r' S (c₁ + c₂)) :=
begin
  rw continuous_iff,
  intros M,
  have : truncate M ∘ (λ x : Mbar r' S c₁ × Mbar r' S c₂, Mbar.add x.1 x.2) =
    (λ x : (Mbar r' S c₁ × Mbar r' S c₂), Mbar_bdd.add (truncate M x.1) (truncate M x.2)) := by {ext; refl},
  erw this,
  suffices : continuous (λ x : Mbar_bdd r' ⟨S⟩ c₁ M × Mbar_bdd r' ⟨S⟩ c₂ M, Mbar_bdd.add x.1 x.2),
  { have claim : (λ x : (Mbar r' S c₁ × Mbar r' S c₂), Mbar_bdd.add (truncate M x.1) (truncate M x.2)) =
      (λ x : Mbar_bdd r' ⟨S⟩ c₁ M × Mbar_bdd r' ⟨S⟩ c₂ M, Mbar_bdd.add x.1 x.2) ∘
      (λ x : Mbar r' S c₁ × Mbar r' S c₂, (truncate M x.1, truncate M x.2)), by {ext, refl},
    rw claim,
    refine continuous.comp this _,
    refine continuous.prod_map continuous_truncate continuous_truncate },
  exact continuous_of_discrete_topology,
end

end topological_structure

lemma Tinv_aux_summable [h0r : fact (0 < r')] (F : Mbar r' S c) (s : S) :
  summable (λ (n : ℕ), abs (↑(Tinv_aux (F.val s) n) * r' ^ n)) :=
begin
  rw summable_mul_right_iff (ne_of_gt h0r),
  have H := F.summable s,
  refine summable_of_norm_bounded _ ((summable_nat_add_iff 1).mpr H) _,
  rintro ⟨i⟩,
  { simp only [abs_nonneg, norm_zero, int.cast_zero, zero_mul, abs_zero, Tinv_aux_zero]},
  { simp only [Tinv_aux_succ, real.norm_eq_abs, abs_mul, pow_add, mul_assoc, pow_one, abs_abs] },
end

def Tinv {r : ℝ} {S : Type u} [fintype S] {c : ℝ} [h0r : fact (0 < r)] :
  Mbar r S c → Mbar r S (c / r) :=
λ F, ⟨λ s, Tinv_aux (F.1 s), λ s, rfl, Tinv_aux_summable F,
begin
  rw [le_div_iff h0r, finset.sum_mul],
  refine le_trans _ F.sum_tsum_le,
  apply finset.sum_le_sum,
  rintro s -,
  rw ← tsum_mul_right _ (Tinv_aux_summable F s),
  conv_rhs { rw [← @sum_add_tsum_nat_add ℝ _ _ _ _ _ 1 (F.summable s)] },
  refine le_add_of_nonneg_of_le (finset.sum_nonneg (λ _ _, abs_nonneg _)) _,
  apply tsum_le_tsum,
  { rintro ⟨i⟩,
    { simp [abs_nonneg] },
    { simp only [Tinv_aux_succ, real.norm_eq_abs, abs_mul, pow_add, mul_assoc,
        pow_one, abs_abs, abs_of_pos h0r] } },
  { rw ← summable_mul_right_iff (ne_of_gt h0r), exact Tinv_aux_summable F s },
  { exact (summable_nat_add_iff 1).mpr (F.summable s) }
end⟩
.
lemma continuous_Tinv (r : ℝ) (S : Type u) [fintype S] (c : ℝ) [h0r : fact (0 < r)] :
  continuous (@Tinv r S _ c _) :=
begin
  rw continuous_iff,
  intro M,
  sorry
end

end Mbar
