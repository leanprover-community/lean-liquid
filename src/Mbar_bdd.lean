import data.fintype.intervals
import data.real.basic
import algebra.big_operators.basic
import category_theory.Fintype

noncomputable theory
open_locale big_operators classical

-- Thanks to Ruben Van de Velde and Yury G. Kudryashov for help with
-- the Ico_finite and Icc_finite lemmas.
-- TODO: Move these somewhere...
open set
lemma Ico_finite (a b : ℤ) : set.finite (Ico a b) := ⟨set.Ico_ℤ_fintype a b⟩
lemma Icc_finite (a b : ℤ) : set.finite (Icc a b) :=
begin
  convert Ico_finite a (b+1),
  ext,
  simp [int.lt_add_one_iff],
end

def Mbar_bdd (r : ℝ) (hr : 0 < r) (S : Fintype) (c : ℝ) (M : ℕ) :=
{F : S → fin (M + 1) → ℤ |
  (∀ s, F s 0 = 0) ∧
  (∑ s i, abs (F s i : ℝ) * r^i.1 ≤ c) }

meta def silly := `[
  intros,
  apply mul_nonneg,
  apply abs_nonneg,
  apply pow_nonneg,
  apply le_of_lt,
  assumption,
  apply finset.mem_univ ]

-- Why is it so hard to prove something is finite?!
-- This proof can probably be cleaned up significantly...
lemma Mbar_bdd_finset {r : ℝ} (hr : 0 < r) {S : Fintype} {c : ℝ} {M : ℕ} :
  fintype (Mbar_bdd r hr S c M) :=
begin
  let MM := Mbar_bdd r hr S c M,
  let MMM := {F : S → fin (M+1) → ℤ | ∀ s i, abs (F s i : ℝ) * r^i.1 ≤ c},
  let ι : MM → MMM := λ F, ⟨F.1,λ s i, _⟩,
  swap,
  { have claim : ∑ i, abs (F.1 s i : ℝ) * r^i.1 ≤ c,
    { have := @finset.single_le_sum S ℝ finset.univ (λ s, ∑ i, abs (F.1 s i : ℝ) * r^i.1) _ _ s _,
      apply le_trans this F.2.2,
      intros x hx,
      apply finset.sum_nonneg,
      silly },
    have e1 := @finset.single_le_sum S ℝ finset.univ (λ s, ∑ i, abs (F.1 s i : ℝ) * r^i.1) _ _ s _,
    have e2 := @finset.single_le_sum (fin (M+1)) ℝ finset.univ (λ i, abs (F.1 s i : ℝ) * r^i.1) _ _ i _,
    exact le_trans e2 (le_trans e1 F.2.2),
    silly,
    intros s hs,
    apply finset.sum_nonneg,
    silly },
  have claim : function.injective ι,
  { intros x y h,
    apply_fun (λ u, u.1) at h,
    ext1,
    assumption },
  suffices : fintype MMM, by exactI fintype.of_injective ι claim,
  let MMMM := Π (s : S) (i : fin (M+1)), { m : ℤ | abs (m : ℝ) * r^i.1 ≤ c},
  let δ : MMM → MMMM := λ m s i, ⟨m.1 s i, _⟩,
  swap,
  apply m.2,
  have claim2 : function.injective δ,
  { intros x y h,
    dsimp [δ] at h,
    replace h := congr_fun h,
    ext s i,
    specialize h s,
    replace h := congr_fun h,
    specialize h i,
    dsimp at h,
    apply_fun (λ u, u.1) at h,
    assumption },
  suffices : fintype MMMM, by exactI fintype.of_injective δ claim2,
  suffices claim3 : ∀ (s : S), fintype (Π (i : fin (M+1)), {m : ℤ | abs (m : ℝ) * r^i.1 ≤ c}),
    by exact @pi.fintype S (λ s, Π (i : fin (M+1)), {m : ℤ | abs (m : ℝ) * r^i.1 ≤ c}) _ _ claim3,
  intro s,
  suffices : ∀ i : fin (M+1), fintype {m : ℤ | abs (m : ℝ) * r^i.1 ≤ c},
    by exact @pi.fintype (fin (M+1)) (λ i, {m : ℤ | abs (m : ℝ) * r^i.1 ≤ c}) _ _ this,
  intros i,
  suffices : {m : ℤ | abs (m : ℝ) * r^i.1 ≤ c}.finite, by exact finite.fintype this,
  have : {m : ℤ | abs (m : ℝ) * r^i.1 ≤ c } = {m : ℤ | abs (m : ℝ) ≤ (c * (r^i.1)⁻¹) },
  { ext,
    dsimp,
    have c1 : 0 ≤ r^i.1, apply pow_nonneg, apply le_of_lt, assumption,
    have c2 : 0 ≤ (r^i.1)⁻¹, rw inv_nonneg, apply pow_nonneg, apply le_of_lt, assumption,
    have c3 : r^i.1 ≠ 0, apply pow_ne_zero, linarith,
    split,
    { intro h,
      convert mul_le_mul_of_nonneg_right h c2,
      erw [mul_assoc, mul_inv_cancel c3, mul_one] },
    { intro h,
      convert mul_le_mul_of_nonneg_right h c1,
      erw [mul_assoc, inv_mul_cancel c3, mul_one] } },
  rw this,
  convert Icc_finite _ _,
  ext,
  rw [←int.cast_abs, ←le_floor, abs_le],
end
