import pseudo_normed_group.basic
import analysis.normed_space.basic

namespace normed_group

instance (V : Type*) [normed_group V] : pseudo_normed_group V :=
{ filtration := λ c, {v | ∥v∥ ≤ c},
  filtration_mono := λ c₁ c₂ h v (hv : ∥v∥ ≤ c₁), le_trans hv h,
  zero_mem_filtration := λ c, by simp only [set.mem_set_of_eq, norm_zero, nnreal.zero_le_coe],
  neg_mem_filtration := λ c v hv, by simpa only [set.mem_set_of_eq, norm_neg] using hv,
  add_mem_filtration := λ c₁ c₂ v₁ v₂ hv₁ hv₂,
    calc ∥v₁ + v₂∥
        ≤ ∥v₁∥ + ∥v₂∥ : norm_add_le _ _
    ... ≤ c₁ + c₂ : add_le_add hv₁ hv₂ }

variables {V : Type*} [normed_group V]

open pseudo_normed_group

lemma mem_filtration_nnnorm (v : V) : v ∈ filtration V (nnnorm v) :=
show ∥v∥ ≤ ∥v∥, from le_rfl

end normed_group
