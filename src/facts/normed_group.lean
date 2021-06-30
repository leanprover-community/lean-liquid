import analysis.normed_space.basic

variables {V : Type*} [semi_normed_group V]

instance fact_nnnorm_add_le (v w : V) :
  fact (∥v + w∥₊ ≤ ∥v∥₊ + ∥w∥₊) :=
⟨nnnorm_add_le _ _⟩
