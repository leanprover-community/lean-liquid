import polyhedral_lattice.basic

noncomputable theory
open_locale big_operators classical nnreal

local attribute [-instance] add_comm_monoid.nat_semimodule add_comm_group.int_module

@[nolint unused_arguments]
def rescale (N : ℝ≥0) (V : Type*) := V

namespace rescale

variables {N : ℝ≥0} {V : Type*}

instance [i : add_comm_monoid V] : add_comm_monoid (rescale N V) := i
instance [i : add_comm_group V] : add_comm_group (rescale N V) := i

def of : V ≃ rescale N V := equiv.refl _

section normed_group

instance [has_norm V] : has_norm (rescale N V) :=
{ norm := λ v, ∥of.symm v∥/N }

lemma norm_def [has_norm V] (v : rescale N V) : ∥v∥ = ∥of.symm v∥/N := rfl

-- remove the `fact` once we have `seminormed_group`
instance [hN : fact (0 < N)] [normed_group V] : normed_group (rescale N V) :=
normed_group.of_core (rescale N V)
{ norm_eq_zero_iff := λ v,
  begin
    have aux : (N:ℝ) ≠ 0 := ne_of_gt hN,
    simp only [norm_def, div_eq_zero_iff, aux, or_false],
    exact norm_eq_zero -- defeq abuse
  end,
  triangle := λ v w,
  begin
    simp only [norm_def, ← add_div],
    exact div_le_div_of_le (le_of_lt hN) (norm_add_le _ _), -- defeq abuse
  end,
  norm_neg := λ v, by { simp only [norm_def], congr' 1, exact norm_neg _ /- defeq abuse -/ } }

lemma nnnorm_def [hN : fact (0 < N)] [normed_group V] (v : rescale N V) :
  nnnorm v = nnnorm (of.symm v) / N := rfl

end normed_group

section polyhedral_lattice

instance (Λ : Type*) [hN : fact (0 < N)] [polyhedral_lattice Λ] :
  polyhedral_lattice (rescale N Λ) :=
{ nat_semimodule := by { delta rescale, apply_instance },
  int_semimodule := by { delta rescale, apply_instance },
  is_scalar_tower := by { delta rescale, apply_instance },
  finite_free := by { delta rescale, exact polyhedral_lattice.finite_free },
  polyhedral :=
  begin
    obtain ⟨ι, _inst_ι, l, hl⟩ := polyhedral_lattice.polyhedral Λ,
    refine ⟨ι, _inst_ι, l, _⟩,
    intro x,
    obtain ⟨d, hd, c, H1, H2⟩ := hl x,
    refine ⟨d, hd, c, H1, _⟩,
    simp only [norm_def, ← mul_div_assoc, ← finset.sum_div],
    congr' 1, -- defeq abuse
  end }

end polyhedral_lattice

end rescale
