import ring_theory.power_series
import data.real.basic
import algebra.big_operators.basic
import topology.algebra.infinite_sum
import data.finset.basic
import data.equiv.basic
import analysis.normed_space.basic
import analysis.specific_limits
import .Mbar_bdd
/-

Scholze Analytic.pdf

p57, S finite

Mbar_r'(S)_{<=c}={(sum_{n≥1}a_{n,s}T^n)[s] | sum_{s,n}|a_{n,s}|r^n<=c}

-/

universe u

noncomputable theory
open_locale big_operators

open power_series

/-- `Mbar r' S c` is the set of power series
`F_s = ∑ a_{n,s}T^n ∈ ℤ[[T]]` such that `∑_{n,s} |a_{n,s}|r'^n ≤ c` -/
def Mbar (r' : ℝ) (S : Type u) [fintype S] (c : ℝ) :=
{F : S → ℕ → ℤ // (∀ s, F s 0 = 0) ∧
  (∀ s, summable (λ n, abs ((F s n : ℝ) * r'^n))) ∧
  (∑ s, ∑' n, (abs ((F s n : ℝ) * r'^n))) ≤ c }

variables {r' : ℝ} {S : Type u} [fintype S] {c c₁ c₂ : ℝ}

def Mbar.constant_coeff_eq_zero (x : Mbar r' S c) := x.2.1

def Mbar.summable (x : Mbar r' S c) := x.2.2.1

def Mbar.sum_tsum_le (x : Mbar r' S c) := x.2.2.2

def Mbar.cast_le (h : c₁ ≤ c₂) (x : Mbar r' S c₁) : Mbar r' S c₂ :=
⟨x.1, x.constant_coeff_eq_zero, x.summable, x.sum_tsum_le.trans h⟩

-- lemma abs_mul_pow_pos {x r : ℝ} (hr : 0 < r) {n : ℕ} :
--   abs (x * r ^ n) = abs x * r ^ n :=
-- by rw [abs_mul, abs_of_pos (pow_pos hr _)]

noncomputable def Mbar.add (hr' : 0 < r') :
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
  refine ⟨_, hFGs, _⟩,
  { intro s,
    simp [hF0 s, hG0 s] },
  { refine le_trans _ (add_le_add hFsc hGsc),
    rw ← finset.sum_add_distrib,
    apply finset.sum_le_sum,
    rintro s -,
    rw ← tsum_add (hFs s) (hGs s),
    refine tsum_le_tsum _ (hFGs s) _,
    { intro n,
      convert abs_add _ _,
      simp [add_mul] },
    { exact summable.add (hFs s) (hGs s) } }
end⟩

lemma sum_fin_eq {M : ℕ} (f : ℕ → ℝ) : ∑ i in finset.range M, f i = ∑ (i : fin M), f i :=
@finset.sum_bij' ℕ ℝ (fin M) _ (finset.range M) finset.univ f (λ i, f i)
  (λ a ha, ⟨a, finset.mem_range.mp ha⟩) (λ a ha, finset.mem_univ _) (λ a ha, rfl)
  (λ a _, a) (λ a ha, finset.mem_range.mpr a.2) (λ a ha, rfl) (λ a ha, by simp)

def Tinv_aux {R : Type*} [has_zero R] : (ℕ → R) → ℕ → R := λ F n, if n = 0 then 0 else F (n + 1)
/-
namespace power_series

def truncate (F : power_series ℤ) (M : ℕ) : fin (M+1) → ℤ :=
λ i, coeff _ i F

variables {R : Type*} [add_monoid R]

-- move this
-- is this the correct def??
def Tinv : power_series R →+ power_series R :=
{ to_fun := λ F, mk $ λ n, if n = 0 then 0 else coeff R (n+1) F,
  map_zero' := by { ext n, simp only [if_t_t, coeff_mk, add_monoid_hom.map_zero] },
  map_add' :=
  begin
    intros F G,
    ext n,
    simp only [coeff_mk, add_monoid_hom.map_add],
    split_ifs,
    { rw add_zero },
    { refl }
  end }

lemma Tinv_def (F : power_series R) :
  Tinv F = mk (λ n, if n = 0 then 0 else coeff R (n+1) F) := rfl

@[simp] lemma coeff_zero_Tinv (F : power_series R) :
  coeff R 0 (Tinv F) = 0 :=
by rw [Tinv_def, coeff_mk, if_pos rfl]

@[simp] lemma constant_coeff_Tinv {R : Type*} [semiring R] (F : power_series R) :
  constant_coeff R (Tinv F) = 0 :=
by rw [← coeff_zero_eq_constant_coeff_apply, coeff_zero_Tinv]

@[simp] lemma coeff_succ_Tinv (n : ℕ) (F : power_series R) :
  coeff R (n+1) (Tinv F) = coeff R (n+2) F :=
by rw [Tinv_def, coeff_mk, if_neg (nat.succ_ne_zero n)]

@[simp] lemma coeff_Tinv_of_pos (n : ℕ) (h : 0 < n) (F : power_series R) :
  coeff R n (Tinv F) = coeff R (n+1) F :=
by { obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h, rw [add_comm, coeff_succ_Tinv] }

@[simp] lemma Tinv_monomial_zero (r : R) :
  Tinv (monomial R 0 r) = 0 :=
by { ext n, simp only [Tinv_def, coeff_mk, add_monoid_hom.map_zero, coeff_monomial,
    if_t_t, add_eq_zero_iff, if_false, one_ne_zero, and_false] }

@[simp] lemma Tinv_monomial_one (r : R) :
  Tinv (monomial R 1 r) = 0 :=
begin
  ext n,
  simp only [Tinv_def, coeff_mk, add_monoid_hom.map_zero, coeff_monomial],
  split_ifs with h1 h2; try { refl },
  cases h2, contradiction
end

@[simp] lemma Tinv_monomial_add_two (n : ℕ) (r : R) :
  Tinv (monomial R (n+2) r) = (monomial R (n+1) r) :=
begin
  ext k,
  simp only [Tinv_def, coeff_mk, add_monoid_hom.map_zero, coeff_monomial],
  split_ifs with h1 h2 h3; try { refl <|> cases h2 <|> cases h3 <|> cases h },
  { exact (nat.succ_ne_zero _ h1).elim },
  { contradiction },
  { contradiction }
end

@[simp] lemma Tinv_monomial_of_two_le (n : ℕ) (hn : 2 ≤ n) (r : R) :
  Tinv (monomial R n r) = (monomial R (n-1) r) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le hn,
  rw [add_comm, Tinv_monomial_add_two],
  refl
end

end power_series
-/

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
lemma eq_iff_truncate_eq {hr : 0 < r'} (x y : Mbar r' S c)
  (cond : ∀ M, truncate M x = truncate M y) : x = y :=
begin
  ext s n,
  change (truncate n x).1 s ⟨n, by linarith⟩ = (truncate n y).1 s ⟨n,_⟩,
  rw cond,
end

def mk_seq (T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M) : S → ℕ → ℤ :=
  λ s n, (T n).1 s ⟨n, by linarith⟩

lemma mk_seq_zero {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M} (s : S) : mk_seq T s 0 = 0 := (T 0).2.1 s

lemma mk_seq_eq_of_compat {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), transition r' h (T N) = T M)
  {s : S} {n : ℕ} {M : ℕ} (hnM : n < M + 1) :
  mk_seq T s n = (T M).1 s ⟨n, hnM⟩ :=
begin
  have hnM : n ≤ M := nat.lt_succ_iff.mp hnM,
  unfold mk_seq,
  rw ← compat n M hnM,
  apply transition_eq,
end

lemma mk_seq_sum_range_eq (T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M)
  (compat : ∀ (M N : ℕ) (h : M ≤ N), transition r' h (T N) = T M) (s : S) (n) :
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
  (compat : ∀ (M N : ℕ) (h : M ≤ N), transition r' h (T N) = T M) (s : S) :
  _root_.summable (λ (n : ℕ), abs (↑(mk_seq T s n) * r' ^ n)) :=
begin
  refine @summable_of_sum_range_le (λ n, abs ((mk_seq T s n : ℝ) * r'^n)) c (λ _, abs_nonneg _) (λ n, _),
  cases n,
  { exact le_trans (by simp) (nonneg_of_Mbar_bdd (T 0)) },
  { rw mk_seq_sum_range_eq T compat s n,
    refine le_trans _ (T n).2.2,
    refine finset.single_le_sum (λ _ _, _) (finset.mem_univ s),
    exact finset.sum_nonneg (λ _ _, abs_nonneg _) },
end

open filter
lemma mk_seq_tendsto {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), transition r' h (T N) = T M) :
  tendsto (λ (n : ℕ), ∑ (s : S), ∑  i in finset.range n, abs ((mk_seq T s i : ℝ) * r'^i))
  at_top (nhds $ ∑ (s : S), ∑' n, abs ((mk_seq T s n : ℝ) * r'^n)) := tendsto_finset_sum _ $
λ s _, has_sum.tendsto_sum_nat $ summable.has_sum $ mk_seq_summable compat s

lemma mk_seq_sum_le {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), transition r' h (T N) = T M) :
  (∑ s, ∑' (n : ℕ), abs (↑(mk_seq T s n) * r' ^ n)) ≤ c :=
begin
  refine le_of_tendsto (mk_seq_tendsto compat) (eventually_of_forall _),
  rintros (_|n),
  { simp [nonneg_of_Mbar_bdd (T 0)] },
  { convert (T n).2.2,
    funext,
    rw mk_seq_sum_range_eq T compat s n,
    refl }
end

lemma truncate_mk_seq {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), transition r' h (T N) = T M) (M : ℕ) :
  truncate M ⟨mk_seq T, mk_seq_zero, mk_seq_summable compat, mk_seq_sum_le compat⟩ = T M :=
begin
  ext s ⟨i, hi⟩,
  exact mk_seq_eq_of_compat compat _,
end

-- Surjectivity
lemma exists_of_compat {hr : 0 < r'} (T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M)
  (compat : ∀ (M N : ℕ) (h : M ≤ N), transition r' h (T N) = T M) :
  ∃ (F : Mbar r' S c), ∀ M, truncate M F = T M :=
⟨⟨mk_seq T, mk_seq_zero, mk_seq_summable compat, mk_seq_sum_le compat⟩, truncate_mk_seq compat⟩

def Tinv {r : ℝ} {S : Type u} [fintype S] {c : ℝ} (h0r : 0 < r) :
  Mbar r S c → Mbar r S (c / r) :=
λ F, ⟨λ s, Tinv_aux (F.1 s), λ s, rfl, sorry, sorry⟩

-- This code of Johan's will be useful for the two sorrys above
-- ⟨λ s, power_series.Tinv (x.1 s),
-- begin
--   have hsummable : _ := _,
--   refine ⟨_, hsummable, _⟩,
--   { intro s, exact power_series.constant_coeff_Tinv _ },
--   { rw [le_div_iff h0r, finset.sum_mul],
--     refine le_trans _ x.sum_tsum_le,
--     apply finset.sum_le_sum,
--     rintro s -,
--     rw ← tsum_mul_right _ (hsummable s),
--     conv_rhs { rw [← @sum_add_tsum_nat_add ℝ _ _ _ _ _ 1 (x.summable s)] },
--     refine le_add_of_nonneg_of_le (finset.sum_nonneg _) _,
--     { intros, exact abs_nonneg _ },
--     apply tsum_le_tsum,
--     { -- we should be able to dedup parts of this with the block that follows it
--       rintro ⟨i⟩,
--       { simpa only [int.cast_zero, zero_mul, coeff_zero_eq_constant_coeff,
--           ring_hom.coe_add_monoid_hom, abs_zero, pow_one, zero_add,
--           power_series.constant_coeff_Tinv, subtype.val_eq_coe] using abs_nonneg _ },
--       { simp only [nat.succ_pos', normed_field.norm_mul, power_series.coeff_Tinv_of_pos,
--         subtype.val_eq_coe, pow_succ', ← real.norm_eq_abs, mul_assoc, norm_norm,
--         real.norm_of_nonneg h0r.le] } },
--     { rw ← summable_mul_right_iff h0r.ne.symm, exact hsummable _ },
--     { exact (summable_nat_add_iff 1).mpr (x.summable s) } },
--   { intro s, rw summable_mul_right_iff h0r.ne.symm,
--     have H := x.summable s,
--     refine summable_of_norm_bounded _ ((summable_nat_add_iff 1).mpr H) _,
--     rintro ⟨i⟩,
--     { simpa only [norm_zero, int.cast_zero, zero_mul, coeff_zero_eq_constant_coeff,
--         ring_hom.coe_add_monoid_hom, abs_zero, pow_one, zero_add, power_series.constant_coeff_Tinv,
--         subtype.val_eq_coe] using abs_nonneg _ },
--     { simp only [nat.succ_pos', normed_field.norm_mul, power_series.coeff_Tinv_of_pos,
--         subtype.val_eq_coe, pow_succ', ← real.norm_eq_abs, mul_assoc, norm_norm] } },
-- end⟩

end Mbar
