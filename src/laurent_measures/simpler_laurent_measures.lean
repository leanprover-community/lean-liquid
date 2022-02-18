import laurent_measures.basic
import laurent_measures.aux_lemmas
import analysis.special_functions.pow
import laurent_measures.thm69

open nnreal laurent_measures aux_thm69
open_locale nnreal

noncomputable theory

namespace slm
section slm

--  This is the same as before, from here to...
-- parameter {p : ℝ≥0}

/--  This is the same `r` as before. -/
-- def r : ℝ≥0 := (1 / 2) ^ (p:ℝ)

-- lemma r_pos : 0 < r :=
-- suffices 0 < (2 : ℝ≥0)⁻¹ ^ (p : ℝ), by simpa [r],
-- rpow_pos (nnreal.inv_pos.mpr zero_lt_two)

-- lemma r_lt_one [fact(0 < p)] : r < 1 :=
-- begin
--   refine rpow_lt_one zero_le' (half_lt_self one_ne_zero) _,
--   rw nnreal.coe_pos,
--   exact fact.out _
-- end

variables {r : ℝ≥0} [fact (0 < r)] [fact (r < 1)]

local notation `ℒ` := laurent_measures r

variables {S : Fintype}

/--  Let `F : ℒ S` be a Laurent measure.  `laurent_measures.d` chooses a bound `d ∈ ℤ` for `F`,
such that, for all `s : S`, the sequence `F s` is zero from `d-1` and below. -/
def laurent_measures.d (F : ℒ S) : ℤ :=
(exists_bdd_filtration (fact.out _ : 0 < r) (fact.out _ : r < 1) F).some

lemma lt_d_eq_zero (F : ℒ S) (s : S) (n : ℤ) :
  n < F.d → F s n = 0 :=
(exists_bdd_filtration (fact.out _ : 0 < r) (fact.out _ : r < 1) F).some_spec s n
--  ... here!


section new_stuff
/--  Simpler Laurent measures? -/
structure slm (r : ℝ≥0) (S : Fintype) :=
(to_fun    : S → ℤ → ℤ)
(d         : ℤ)
(summable' : ∀ s, summable (λ n : ℕ, ∥to_fun s n∥₊ * r ^ n))
(zero_lt_d : ∀ s n, n < d → to_fun s n = 0)

/--  A "usual" Laurent Measure `F : ℒ S` gives rise to a Simple Laurent Measure of type `slm S`. -/
def _root_.laurent_measures.to_slm (F : ℒ S) : slm S :=
{ to_fun    := F.to_fun,
  d         := F.d,
  zero_lt_d := lt_d_eq_zero F,
  summable' := begin
    refine λ s, summable_coe.mp _,
    convert ((@int_summable_iff _ _ _ _ _ (λ (n : ℤ), ∥F.to_fun s n∥ * slm.r ^ n)).mp _).1,
    { ext, simp },
    { convert summable_coe.mpr (F.summable' s),
      simp }
  end }

/--  A Simple Laurent Measure `F : slm S` "usual" Laurent Measure of type `ℒ S`. -/
--  The "main" input is `int_summable_iff`, proving that a series over `ℤ` is summable if and only
--  if both its restrictions to `ℕ` and to "`-ℕ`" are summable.
def slm.to_laurent_measures (F : slm r S) : ℒ S :=
{ to_fun := F.to_fun,
  summable' := begin
    refine λ s, summable_coe.mp _,
    convert ((@int_summable_iff _ _ _ _ _ (λ (n : ℤ), ∥F.to_fun s n∥ * r ^ n)).mpr _),
    { simp },
    { refine ⟨_, summable_of_eventually_zero (λ (n : ℤ), ∥F.to_fun s n∥ * ↑r ^ n) F.d (λ n nd, _)⟩,
      { convert summable_coe.mpr (F.summable' s),
        simp },
      { simp [F.zero_lt_d s n nd] } }
  end }
lemma slm_lm_to_fun_eq (F : slm S) : F.to_fun = F.to_laurent_measures.to_fun := rfl

-- lemma lm_slm_to_fun_eq (F : ℒ S) : F.to_fun = F.to_slm.to_fun := rfl

end new_stuff

end slm
end slm
