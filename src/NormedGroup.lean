import analysis.normed_space.basic
import category_theory.concrete_category.bundled_hom
import algebra.punit_instances

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

/-- The category of normed abelian groups and continuous group homomorphisms. -/
def NormedGroup : Type (u+1) := bundled normed_group

set_option old_structure_cmd true

/-- A morphism of normed abelian groups is a continuous group homomorphism. -/
structure normed_group_hom (V W : Type*) [normed_group V] [normed_group W] extends
  add_monoid_hom V W, continuous_map V W.

namespace normed_group_hom

attribute [continuity] normed_group_hom.continuous_to_fun

variables {V V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group V₁] [normed_group V₂] [normed_group V₃]

instance : has_coe_to_fun (normed_group_hom V₁ V₂) := ⟨_, normed_group_hom.to_fun⟩

variables {f g : normed_group_hom V₁ V₂}

protected lemma continuous (f : normed_group_hom V₁ V₂) : continuous f := f.continuous_to_fun

@[continuity] lemma coe_continuous : continuous (f : V₁ → V₂) := f.continuous_to_fun

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

instance : inhabited (normed_group_hom V₁ V₂) :=
⟨{ continuous_to_fun := continuous_const, .. (0 : V₁ →+ V₂) }⟩

lemma coe_inj ⦃f g : normed_group_hom V₁ V₂⦄ (h : (f : V₁ → V₂) = g) : f = g :=
by cases f; cases g; cases h; refl

/-- The identity as a continuous map. -/
def id : normed_group_hom V V :=
{ .. add_monoid_hom.id V, .. continuous_map.id }

/-- The composition of continuous maps, as a continuous map. -/
def comp (g : normed_group_hom V₂ V₃) (f : normed_group_hom V₁ V₂) :
  normed_group_hom V₁ V₃ :=
{ .. g.to_add_monoid_hom.comp f.to_add_monoid_hom, .. g.to_continuous_map.comp f.to_continuous_map }

end normed_group_hom

namespace NormedGroup

instance bundled_hom : bundled_hom @normed_group_hom :=
⟨@normed_group_hom.to_fun, @normed_group_hom.id, @normed_group_hom.comp, @normed_group_hom.coe_inj⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] NormedGroup

/-- Construct a bundled `NormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [normed_group M] : NormedGroup := bundled.of M

noncomputable
instance : inhabited NormedGroup := ⟨of punit⟩

instance (M : NormedGroup) : normed_group M := M.str

@[simp] lemma coe_of (R : Type u) [normed_group R] : (NormedGroup.of R : Type u) = R := rfl

end NormedGroup
