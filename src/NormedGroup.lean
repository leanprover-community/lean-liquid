import algebra.punit_instances
import category_theory.concrete_category.bundled_hom
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.kernels
import category_theory.limits.creates

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

section kernels

open category_theory.limits

def kernel_cone {V W : NormedGroup} (f : V ⟶ W) : limits.fork f 0 :=
@fork.of_ι _ _ _ _ _ _ (of f.ker) (normed_group_hom.ker.incl f) $
begin
  ext v,
  simp only [normed_group_hom.ker.incl_to_fun, pi.zero_apply, coe_comp, normed_group_hom.coe_zero],
  exact v.2
end

instance : limits.has_kernels.{u (u+1)} NormedGroup :=
{ has_limit := λ V W f,
  { exists_limit := nonempty.intro
    { cone := kernel_cone.{u u} f,
      is_limit := fork.is_limit.mk _
        (λ c, normed_group_hom.ker.lift (fork.ι c) _ $
        show _ ≫ f = 0,
        by simp only [fork.ι_eq_app_zero, fork.condition c, comp_zero])
        (λ c, normed_group_hom.ker.incl_comp_lift _ _ _)
        (λ c g h, by { ext x, dsimp, rw ← h, refl }) } } }

end kernels

end NormedGroup
