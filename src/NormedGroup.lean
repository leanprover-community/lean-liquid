import algebra.punit_instances
import category_theory.concrete_category.bundled_hom
import category_theory.limits.shapes.zero

import .normed_group_hom

/-!
# The category of normed abelian groups and continuous group homomorphisms

-/

universes u v

-- move this
section for_mathlib

instance punit.uniform_space : uniform_space punit := ⊥

noncomputable
instance punit.metric_space : metric_space punit :=
{ dist := λ _ _, 0,
  dist_self := λ _, rfl,
  dist_comm := λ _ _, rfl,
  eq_of_dist_eq_zero := λ _ _ _, subsingleton.elim _ _,
  dist_triangle := λ _ _ _, show (0:ℝ) ≤ 0 + 0, by rw add_zero,
  .. punit.uniform_space }

noncomputable
instance punit.normed_group : normed_group punit :=
{ norm := function.const _ 0,
  dist_eq := λ _ _, rfl,
  .. punit.add_comm_group, .. punit.metric_space }

end for_mathlib

open category_theory

/-- The category of normed abelian groups and bounded group homomorphisms. -/
def NormedGroup : Type (u+1) := bundled normed_group

namespace NormedGroup

instance bundled_hom : bundled_hom @normed_group_hom :=
⟨@normed_group_hom.to_fun, @normed_group_hom.id, @normed_group_hom.comp, @normed_group_hom.coe_inj⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] NormedGroup

/-- Construct a bundled `NormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [normed_group M] : NormedGroup := bundled.of M

noncomputable
instance : has_zero NormedGroup := ⟨of punit⟩

noncomputable
instance : inhabited NormedGroup := ⟨0⟩

instance (M : NormedGroup) : normed_group M := M.str

@[simp] lemma coe_of (R : Type u) [normed_group R] : (NormedGroup.of R : Type u) = R := rfl

instance : limits.has_zero_morphisms.{u (u+1)} NormedGroup :=
{ comp_zero' := by { intros, apply normed_group_hom.zero_comp },
  zero_comp' := by { intros, apply normed_group_hom.comp_zero } }

end NormedGroup
