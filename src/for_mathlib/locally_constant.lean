import topology.category.Profinite
import topology.algebra.group_completion
import topology.metric_space.completion

noncomputable theory

variables (S S₁ S₂ V : Type*)
variables
  [topological_space S] [compact_space S] [t2_space S] [totally_disconnected_space S]
  [topological_space S₁] [compact_space S₁] [t2_space S₁] [totally_disconnected_space S₁]
  [topological_space S₂] [compact_space S₂] [t2_space S₂] [totally_disconnected_space S₂]

-- move this
section for_mathlib

namespace uniform_space
namespace completion

instance [uniform_space V] [has_norm V] :
  has_norm (completion V) :=
{ norm := completion.extension has_norm.norm }

lemma uniform_continuous_norm [normed_group V] : uniform_continuous (norm : V → ℝ) :=
begin
  rw metric.uniform_continuous_iff,
  intros ε hε,
  use [ε, hε],
  intros x y hxy,
  rw dist_eq_norm at hxy ⊢,
  calc ∥∥x∥ - ∥y∥∥
      = abs(∥x∥ - ∥y∥) : by rw real.norm_eq_abs
  ... ≤ ∥x - y∥ : abs_norm_sub_norm_le x y
  ... < ε : hxy
end

@[simp] lemma norm_coe {V} [normed_group V] (v : V) :
  ∥(v : completion V)∥ = ∥v∥ :=
completion.extension_coe (uniform_continuous_norm _) v

instance [normed_group V] : normed_group (completion V) :=
{ dist_eq :=
  begin
    intros x y,
    apply completion.induction_on₂ x y; clear x y,
    { refine is_closed_eq (completion.uniform_continuous_extension₂ _).continuous _,
      refine continuous.comp _ continuous_sub,
      exact completion.continuous_extension },
    { intros x y,
      -- the following line needs `completion.coe_sub`
      rw [sub_eq_add_neg, ← completion.coe_neg, ← completion.coe_add, ← sub_eq_add_neg, norm_coe],
      -- the rest should be `dist_coe_coe`
      show completion.extension₂ _ _ _ = _,
      rw [completion.extension₂_coe_coe, dist_eq_norm],
      { exact uniform_continuous_dist } }
  end,
  .. (show add_comm_group (completion V), by apply_instance),
  .. (show metric_space (completion V), by apply_instance) }

end completion
end uniform_space

end for_mathlib
#lint- only unused_arguments def_lemma doc_blame
