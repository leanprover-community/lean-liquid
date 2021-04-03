import rescale.basic

noncomputable theory
open_locale big_operators classical nnreal

local attribute [-instance] add_comm_monoid.nat_semimodule add_comm_group.int_module

namespace rescale

variables {N : ℝ≥0} {V : Type*}

instance [has_norm V] : has_norm (rescale N V) :=
{ norm := λ v, ∥of.symm v∥/N }

lemma norm_def [has_norm V] (v : rescale N V) : ∥v∥ = ∥of.symm v∥/N := rfl

-- remove the `fact` once we have `seminormed_group`
instance [hN : fact (0 < N)] [normed_group V] : normed_group (rescale N V) :=
normed_group.of_core (rescale N V)
{ norm_eq_zero_iff := λ v,
  begin
    have aux : (N:ℝ) ≠ 0 := ne_of_gt hN.out,
    simp only [norm_def, div_eq_zero_iff, aux, or_false],
    exact norm_eq_zero -- defeq abuse
  end,
  triangle := λ v w,
  begin
    simp only [norm_def, ← add_div],
    exact div_le_div_of_le hN.out.le (norm_add_le _ _), -- defeq abuse
  end,
  norm_neg := λ v, by { simp only [norm_def], congr' 1, exact norm_neg _ /- defeq abuse -/ } }

lemma nnnorm_def [hN : fact (0 < N)] [normed_group V] (v : rescale N V) :
  nnnorm v = nnnorm (of.symm v) / N := rfl

end rescale
