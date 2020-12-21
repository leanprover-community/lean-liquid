import locally_constant.analysis
import topology.category.Profinite
import topology.algebra.group_completion
import topology.metric_space.completion

noncomputable theory

variables (V S S₁ S₂ : Type*) [normed_group V]
variables
  [topological_space S] [compact_space S] [t2_space S] [totally_disconnected_space S]
  [topological_space S₁] [compact_space S₁] [t2_space S₁] [totally_disconnected_space S₁]
  [topological_space S₂] [compact_space S₂] [t2_space S₂] [totally_disconnected_space S₂]

-- move this
section for_mathlib

namespace uniform_space
namespace completion

instance (V : Type*) [uniform_space V] [has_norm V] :
  has_norm (completion V) :=
{ norm := completion.extension has_norm.norm }

instance : normed_group (completion V) :=
{ dist_eq :=
  begin
    intros x y,
    apply completion.induction_on₂ x y; clear x y,
    { sorry },
    { intros x y,
      show completion.extension₂ _ _ _ = completion.extension _ _,
      rw [sub_eq_add_neg, ← completion.coe_neg, ← completion.coe_add, ← sub_eq_add_neg],
      rw [completion.extension₂_coe_coe, completion.extension_coe, dist_eq_norm],
      { exact sorry },
      { exact uniform_continuous_dist } }
  end,
  .. (show add_comm_group (completion V), by apply_instance),
  .. (show metric_space (completion V), by apply_instance) }

end completion
end uniform_space

end for_mathlib

local attribute [instance] locally_constant.normed_group

@[derive [add_comm_group, metric_space, normed_group]]
def hat := uniform_space.completion (locally_constant S V)

namespace hat
open uniform_space

def comap (f : S₁ → S₂) : hat V S₂ → hat V S₁ :=
completion.map $ locally_constant.comap f

end hat
