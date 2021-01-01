import Mbar.basic
/-!

## $\overline{\mathcal{M}}_{r'}(S)$

This file contains a definition of ℳ-barᵣ'(S) as defined on p57 of Analytic.pdf .

## Implementation issues

We model Tℤ[[T]] as functions ℕ → ℤ which vanish at 0.

-/

universe u

noncomputable theory
open_locale big_operators

open power_series

variables {r' : ℝ} {S : Type u} [fintype S] {c c₁ c₂ c₃ : ℝ}

namespace Mbar_le

instance has_coe_to_fun : has_coe_to_fun (Mbar_le r' S c) := ⟨_, Mbar_le.to_fun⟩

@[simp] lemma coe_mk (x h₁ h₂ h₃) : ((⟨x, h₁, h₂, h₃⟩ : Mbar_le r' S c) : S → ℕ → ℤ) = x := rfl

@[simp] protected lemma coeff_zero (x : Mbar_le r' S c) (s : S) : x s 0 = 0 := x.coeff_zero' s

protected lemma summable (x : Mbar_le r' S c) (s : S) :
  summable (λ n, abs ((x s n : ℝ) * r'^n)) := x.summable' s

protected lemma sum_tsum_le (x : Mbar_le r' S c) :
  (∑ s, ∑' n, (abs ((x s n : ℝ) * r'^n))) ≤ c := x.sum_tsum_le'

protected def cast_le [hc : fact (c₁ ≤ c₂)] (x : Mbar_le r' S c₁) : Mbar_le r' S c₂ :=
⟨x.1, x.coeff_zero, x.summable, x.sum_tsum_le.trans hc⟩

def mk' (x : S → ℕ → ℤ)
  (h : (∀ s, x s 0 = 0) ∧
       (∀ s, summable (λ n, abs ((x s n : ℝ) * r'^n))) ∧
       (∑ s, ∑' n, (abs ((x s n : ℝ) * r'^n))) ≤ c) :
  Mbar_le r' S c :=
{ to_fun := x, coeff_zero' := h.1, summable' := h.2.1, sum_tsum_le' := h.2.2 }

@[simp] lemma coe_mk' (x : S → ℕ → ℤ)
  (h : (∀ s, x s 0 = 0) ∧
       (∀ s, summable (λ n, abs ((x s n : ℝ) * r'^n))) ∧
       (∑ s, ∑' n, (abs ((x s n : ℝ) * r'^n))) ≤ c) :
  ⇑(mk' x h) = x := rfl

@[ext] lemma ext (x y : Mbar_le r' S c) (h : ⇑x = y) : x = y :=
by { cases x, cases y, congr, exact h }

instance [h : fact (0 ≤ c)] : has_zero (Mbar_le r' S c) :=
{ zero :=
  { to_fun := 0,
    coeff_zero' := λ s, rfl,
    summable' := λ s, by simpa using summable_zero,
    sum_tsum_le' := by simpa using h } }

end Mbar_le

-- lemma abs_mul_pow_pos {x r : ℝ} (hr : 0 < r) {n : ℕ} :
--   abs (x * r ^ n) = abs x * r ^ n :=
-- by rw [abs_mul, abs_of_pos (pow_pos hr _)]

variables (c₃)

-- move this
instance fact_le_refl : fact (c ≤ c) := le_rfl

noncomputable def Mbar_le.add [h : fact (c₁ + c₂ ≤ c₃)] :
  Mbar_le r' S c₁ → Mbar_le r' S c₂ → Mbar_le r' S c₃ :=
λ F G, Mbar_le.mk' (F + G)
begin
  have H : _ := _,
  refine ⟨λ s, by simp [F.coeff_zero s, G.coeff_zero s], H, _⟩,
  { refine le_trans _ ((add_le_add F.sum_tsum_le G.sum_tsum_le).trans h),
    rw ← finset.sum_add_distrib,
    refine finset.sum_le_sum _,
    rintro s -,
    rw ← tsum_add (F.summable s) (G.summable s),
    refine tsum_le_tsum _ (H s) (summable.add (F.summable s) (G.summable s)),
    intro n,
    convert abs_add _ _,
    simp [add_mul] },
  { intro s,
    have hFs := F.summable, have hGs := G.summable,
    simp_rw summable_abs_iff at hFs hGs ⊢,
    convert summable.add (hFs s) (hGs s),
    ext n,
    simp [add_mul] }
end

def Mbar_le.add' [fact (c₁ + c₂ ≤ c₃)] : Mbar_le r' S c₁ × Mbar_le r' S c₂ → Mbar_le r' S c₃ :=
λ x, Mbar_le.add c₃ x.1 x.2

noncomputable def Mbar_le.neg (F : Mbar_le r' S c) : Mbar_le r' S c :=
Mbar_le.mk' (-F)
begin
  refine ⟨λ s, by simp [F.coeff_zero s], _, _⟩,
  { intro s, convert F.summable s using 1,
    funext, simp only [neg_mul_eq_neg_mul_symm, pi.neg_apply, abs_neg, int.cast_neg], },
  { convert F.sum_tsum_le,
    funext, simp only [neg_mul_eq_neg_mul_symm, pi.neg_apply, abs_neg, int.cast_neg], }
end

-- move this
-- instance fix_my_name4 (n : ℕ) [fact (0 ≤ c)] : fact (0 ≤ c * n) := sorry

noncomputable def Mbar_le.nsmul :
  Π (n : ℕ) (c' : ℝ) [fact (0 ≤ c')] [fact (c * n ≤ c')], Mbar_le r' S c → Mbar_le r' S c'
| 0     c' h0 h := λ F, by exactI 0
| (n+1) c' h0 h := λ F,
have fact (0 ≤ c' - c),
begin
  simp only [sub_nonneg, fact] at h ⊢,
  contrapose! h,
  have : 0 < c := lt_of_le_of_lt h0 h,
  calc c' < c * 1 : by rwa mul_one
  ... ≤ c * (n + 1 : ℕ) : (mul_le_mul_left this).mpr _,
  simp only [nat.cast_add, nat.cast_one, le_add_iff_nonneg_left, nat.cast_nonneg],
end,
have fact (c * n ≤ c' - c),
  by { rw [le_sub_iff_add_le], simpa only [mul_add, mul_one, nat.cast_add, nat.cast_one] using h },
have fact (c' - c + c ≤ c'), by simpa only [sub_add_cancel] using le_rfl,
by exactI Mbar_le.add _ (Mbar_le.nsmul n (c' - c) F) F

-- move this
-- @[simp] lemma int.abs_neg_succ_of_nat (n : ℕ) :
--   abs (-[1+n]) = n+1 :=

noncomputable def Mbar_le.gsmul :
  Π (n : ℤ) (c' : ℝ) [fact (0 ≤ c')] [fact (c * abs n ≤ c')], Mbar_le r' S c → Mbar_le r' S c'
| (n:ℕ)  c' h0 h := λ F,
have fact (c * n ≤ c'), by simpa only [int.cast_coe_nat, nat.abs_cast] using h,
by exactI Mbar_le.nsmul n c' F
| -[1+n] c' h0 h := λ F,
have fact (c * (n+1:ℕ) ≤ c'),
  by simpa only [int.cast_neg_succ_of_nat, abs_neg, ← nat.cast_add_one, nat.abs_cast] using h,
by exactI Mbar_le.nsmul (n+1) c' F.neg

lemma sum_fin_eq {M : ℕ} (f : ℕ → ℝ) : ∑ i in finset.range M, f i = ∑ (i : fin M), f i :=
@finset.sum_bij' ℕ ℝ (fin M) _ (finset.range M) finset.univ f (λ i, f i)
  (λ a ha, ⟨a, finset.mem_range.mp ha⟩) (λ a ha, finset.mem_univ _) (λ a ha, rfl)
  (λ a _, a) (λ a ha, finset.mem_range.mpr a.2) (λ a ha, rfl) (λ a ha, by simp)

namespace Mbar_le

/-- The truncation map fro Mbar_le to Mbar_bdd -/
@[simps] def truncate (M : ℕ) (F : Mbar_le r' S c) : Mbar_bdd r' ⟨S⟩ c M :=
{ to_fun := λ s n, F s n,
  coeff_zero' := by simp,
  sum_le' :=
  begin
    refine le_trans _ F.sum_tsum_le,
    apply finset.sum_le_sum,
    rintros (s : S) -,
    rw ← sum_fin_eq (λ i, abs ((F s i : ℝ) * r' ^i)),
    exact sum_le_tsum _ (λ _ _, abs_nonneg _) (F.summable s),
  end }

-- /-- The truncation maps commute with the transition maps. -/
-- lemma truncate_transition {hr : 0 < r'} {M N : ℕ} (h : M ≤ N) (x : Mbar_le r' S c) :
--   transition h (truncate hr N x) = truncate hr M x := by tidy

-- Injectivity of the map Mbar_le to limit of Mbar_bdd
lemma eq_iff_truncate_eq (x y : Mbar_le r' S c)
  (cond : ∀ M, truncate M x = truncate M y) : x = y :=
begin
  ext s n,
  change (truncate n x).1 s ⟨n, by linarith⟩ = (truncate n y).1 s ⟨n,_⟩,
  rw cond,
end

lemma truncate_cast_le (M : ℕ) [hc : fact (c₁ ≤ c₂)] (x : Mbar_le r' S c₁) :
  truncate M (@Mbar_le.cast_le r' S _ c₁ c₂ _ x) =
    Mbar_bdd.cast_le (truncate M x) :=
by { ext, refl }

/-- Underlying function of the element of Mbar_le f' S associated to a sequence of
  elements of the truncated Mbars. -/
def mk_seq (T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M) : S → ℕ → ℤ :=
  λ s n, (T n).1 s ⟨n, by linarith⟩

lemma mk_seq_zero {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M} (s : S) : mk_seq T s 0 = 0 :=
(T 0).coeff_zero s

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
    refine le_trans _ (T n).sum_le,
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
  { convert (T n).sum_le,
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
  ∃ (F : Mbar_le r' S c), ∀ M, truncate M F = T M :=
⟨⟨mk_seq T, mk_seq_zero, mk_seq_summable compat, mk_seq_sum_le compat⟩, truncate_mk_seq compat⟩
-/

def of_compat {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) : Mbar_le r' S c :=
⟨mk_seq T, mk_seq_zero, mk_seq_summable compat, mk_seq_sum_le compat⟩

@[simp] lemma truncate_of_compat {T : Π (M : ℕ), Mbar_bdd r' ⟨S⟩ c M}
  (compat : ∀ (M N : ℕ) (h : M ≤ N), Mbar_bdd.transition r' h (T N) = T M) (M : ℕ) :
  truncate M (of_compat compat) = T M :=
begin
  ext s ⟨i, hi⟩,
  exact mk_seq_eq_of_compat compat _,
end

def eqv : Mbar_le r' S c ≃ Mbar_bdd.limit r' ⟨S⟩ c :=
{ to_fun := λ F, ⟨λ N, truncate _ F, by tidy⟩,
  inv_fun := λ F, of_compat F.2,
  left_inv := by tidy,
  right_inv := by tidy }


section topological_structure

instance : topological_space (Mbar_le r' S c) := topological_space.induced eqv (by apply_instance)

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

def homeo : Mbar_le r' S c ≃ₜ Mbar_bdd.limit r' ⟨S⟩ c :=
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

lemma truncate_eq (M : ℕ) : (truncate M : Mbar_le r' S c → Mbar_bdd r' ⟨S⟩ c M) =
  (Mbar_bdd.proj M) ∘ homeo := rfl

instance : t2_space (Mbar_le r' S c) :=
⟨λ x y h, separated_by_continuous homeo.continuous (λ c, h $ homeo.injective c)⟩

instance [fact (0 < r')] : compact_space (Mbar_le r' S c) :=
begin
  constructor,
  rw homeo.embedding.compact_iff_compact_image,
  simp only [set.image_univ, homeomorph.range_coe],
  obtain ⟨h⟩ := (by apply_instance : compact_space (Mbar_bdd.limit r' ⟨S⟩ c)),
  exact h,
end

instance : totally_disconnected_space (Mbar_le r' S c) :=
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

lemma continuous_iff {α : Type*} [topological_space α] (f : α → Mbar_le r' S c) :
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

lemma continuous_truncate {M} : continuous (@truncate r' S _ c M) :=
(continuous_iff id).mp continuous_id _

lemma continuous_add' :
  continuous (Mbar_le.add' (c₁ + c₂) : Mbar_le r' S c₁ × Mbar_le r' S c₂ → Mbar_le r' S (c₁ + c₂)) :=
begin
  rw continuous_iff,
  intros M,
  have : truncate M ∘ (λ x : Mbar_le r' S c₁ × Mbar_le r' S c₂, Mbar_le.add _ x.1 x.2) =
    (λ x : (Mbar_le r' S c₁ × Mbar_le r' S c₂), Mbar_bdd.add (truncate M x.1) (truncate M x.2)) :=
    by {ext; refl},
  erw this,
  suffices : continuous (λ x : Mbar_bdd r' ⟨S⟩ c₁ M × Mbar_bdd r' ⟨S⟩ c₂ M, Mbar_bdd.add x.1 x.2),
  { have claim : (λ x : (Mbar_le r' S c₁ × Mbar_le r' S c₂), Mbar_bdd.add (truncate M x.1) (truncate M x.2)) =
      (λ x : Mbar_bdd r' ⟨S⟩ c₁ M × Mbar_bdd r' ⟨S⟩ c₂ M, Mbar_bdd.add x.1 x.2) ∘
      (λ x : Mbar_le r' S c₁ × Mbar_le r' S c₂, (truncate M x.1, truncate M x.2)), by {ext, refl},
    rw claim,
    refine continuous.comp this _,
    refine continuous.prod_map continuous_truncate continuous_truncate },
  exact continuous_of_discrete_topology,
end

end topological_structure

section Tinv

/-!
### The action of T⁻¹
-/

def Tinv_aux {R : Type*} [has_zero R] : (ℕ → R) → ℕ → R := λ F n, if n = 0 then 0 else F (n + 1)

@[simp] lemma Tinv_aux_zero {R : Type*} [has_zero R] (f : ℕ → R) : Tinv_aux f 0 = 0 := rfl

@[simp] lemma Tinv_aux_ne_zero {R : Type*} [has_zero R] (f : ℕ → R) (i : ℕ) (hi : i ≠ 0) :
  Tinv_aux f i = f (i + 1) :=
if_neg hi

@[simp] lemma Tinv_aux_succ {R : Type*} [has_zero R] (f : ℕ → R) (i : ℕ) :
  Tinv_aux f (i + 1) = f (i + 2) :=
if_neg (nat.succ_ne_zero i)

lemma Tinv_aux_summable [h0r : fact (0 < r')] (F : Mbar_le r' S c) (s : S) :
  summable (λ (n : ℕ), abs (↑(Tinv_aux (F s) n) * r' ^ n)) :=
begin
  rw summable_mul_right_iff (ne_of_gt h0r),
  have H := F.summable s,
  refine summable_of_norm_bounded _ ((summable_nat_add_iff 1).mpr H) _,
  rintro ⟨i⟩,
  { simp only [abs_nonneg, norm_zero, int.cast_zero, zero_mul, abs_zero, Tinv_aux_zero]},
  { simp only [Tinv_aux_succ, real.norm_eq_abs, abs_mul, pow_add, mul_assoc, pow_one, abs_abs] },
end

@[simps]
def Tinv {r : ℝ} {S : Type u} [fintype S] {c : ℝ} [h0r : fact (0 < r)] (F : Mbar_le r S c) :
  Mbar_le r S (c / r) :=
{ to_fun := λ s, Tinv_aux (F s),
  coeff_zero' := λ s, rfl,
  summable' := Tinv_aux_summable F,
  sum_tsum_le' :=
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
  end }

lemma truncate_Tinv {r : ℝ} {S : Type u} [fintype S] {c : ℝ} [h0r : fact (0 < r)]
  (F : Mbar_le r S c) (M : ℕ) :
  truncate M (Tinv F) = Mbar_bdd.Tinv (truncate (M+1) F) :=
begin
  ext s i,
  by_cases hi : i = 0,
  { subst hi, simp only [Mbar_bdd.coeff_zero] },
  { simp only [hi, Tinv_to_fun, Mbar_bdd.Tinv_to_fun, fin.coe_succ, Mbar_bdd.Tinv_aux_ne_zero,
      truncate_to_fun, ne.def, not_false_iff],
    rw Tinv_aux_ne_zero,
    simpa only [fin.ext_iff, fin.coe_zero] using hi }
end

lemma continuous_Tinv (r : ℝ) (S : Type u) [fintype S] (c : ℝ) [h0r : fact (0 < r)] :
  continuous (@Tinv r S _ c _) :=
begin
  rw continuous_iff,
  intro M,
  simp only [function.comp, truncate_Tinv],
  exact continuous_bot.comp continuous_truncate
end

end Tinv

lemma continuous_cast_le (r : ℝ) (S : Type u) [fintype S] (c₁ c₂ : ℝ)
  [h0r : fact (0 < r)] [hc : fact (c₁ ≤ c₂)] :
  continuous (@Mbar_le.cast_le r' S _ c₁ c₂ _) :=
begin
  rw continuous_iff,
  intro M,
  simp only [function.comp, truncate_cast_le],
  exact continuous_bot.comp continuous_truncate
end

end Mbar_le
