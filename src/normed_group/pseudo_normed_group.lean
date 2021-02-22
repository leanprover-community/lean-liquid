import pseudo_normed_group.basic
import analysis.normed_space.basic

open_locale nnreal

namespace normed_group

instance (V : Type*) [normed_group V] : pseudo_normed_group V :=
{ filtration := λ c, {v | nnnorm v ≤ c},
  filtration_mono := λ c₁ c₂ h v (hv : ∥v∥ ≤ c₁), le_trans hv h,
  zero_mem_filtration := λ c, by simp only [set.mem_set_of_eq, nnnorm_zero, zero_le],
  neg_mem_filtration := λ c v hv, by simpa only [set.mem_set_of_eq, nnnorm_neg] using hv,
  add_mem_filtration := λ c₁ c₂ v₁ v₂ hv₁ hv₂,
    calc ∥v₁ + v₂∥
        ≤ ∥v₁∥ + ∥v₂∥ : norm_add_le _ _
    ... ≤ c₁ + c₂ : add_le_add hv₁ hv₂ }

variables {V : Type*} [normed_group V]

open pseudo_normed_group

lemma mem_filtration_nnnorm (v : V) : v ∈ filtration V (nnnorm v) :=
show nnnorm v ≤ nnnorm v, from le_rfl

@[simp] lemma mem_filtration_iff (v : V) (c : ℝ≥0) :
  v ∈ filtration V c ↔ nnnorm v ≤ c := iff.rfl

end normed_group
