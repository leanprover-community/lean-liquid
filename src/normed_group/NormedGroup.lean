import algebra.punit_instances
import category_theory.concrete_category.bundled_hom
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.kernels
import category_theory.limits.creates

import for_mathlib.normed_group_quotient

/-!
# The category of normed abelian groups and continuous group homomorphisms

-/

noncomputable theory

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

@[simp] lemma coe_of (V : Type u) [normed_group V] : (NormedGroup.of V : Type u) = V := rfl

@[simp] lemma coe_id (V : NormedGroup) : ⇑(𝟙 V) = id := rfl

instance : limits.has_zero_morphisms.{u (u+1)} NormedGroup :=
{ comp_zero' := by { intros, apply normed_group_hom.zero_comp },
  zero_comp' := by { intros, apply normed_group_hom.comp_zero } }

lemma iso_isometry_of_norm_noninc {V W : NormedGroup} (i : V ≅ W)
  (h1 : i.hom.norm_noninc) (h2 : i.inv.norm_noninc) :
  isometry i.hom :=
begin
  apply normed_group_hom.isometry_of_norm,
  intro v,
  apply le_antisymm (h1 v),
  calc ∥v∥ = ∥i.inv (i.hom v)∥ : by rw [coe_hom_inv_id]
  ... ≤ ∥i.hom v∥ : h2 _,
end

section equalizers_and_kernels

open category_theory.limits

/-- The equalizer cone for a parallel pair of morphisms of normed groups. -/
def parallel_pair_cone {V W : NormedGroup.{u}} (f g : V ⟶ W) :
  cone (parallel_pair f g) :=
@fork.of_ι _ _ _ _ _ _ (of (f - g).ker) (normed_group_hom.incl (f - g).ker) $
begin
  ext v,
  have : v.1 ∈ (f - g).ker := v.2,
  simpa only [normed_group_hom.incl_apply, pi.zero_apply, coe_comp, normed_group_hom.coe_zero,
    subtype.val_eq_coe, normed_group_hom.mem_ker,
    normed_group_hom.coe_sub, pi.sub_apply, sub_eq_zero] using this
end

instance has_limit_parallel_pair {V W : NormedGroup.{u}} (f g : V ⟶ W) :
  has_limit (parallel_pair f g) :=
{ exists_limit := nonempty.intro
  { cone := parallel_pair_cone f g,
    is_limit := fork.is_limit.mk _
      (λ c, normed_group_hom.ker.lift (fork.ι c) _ $
      show normed_group_hom.comp_hom (f - g) c.ι = 0,
      by { rw [add_monoid_hom.map_sub, add_monoid_hom.sub_apply, sub_eq_zero], exact c.condition })
      (λ c, normed_group_hom.ker.incl_comp_lift _ _ _)
      (λ c g h, by { ext x, dsimp, rw ← h, refl }) } }

instance : limits.has_equalizers.{u (u+1)} NormedGroup :=
@has_equalizers_of_has_limit_parallel_pair NormedGroup _ $ λ V W f g,
  NormedGroup.has_limit_parallel_pair f g

instance : limits.has_kernels.{u (u+1)} NormedGroup :=
by apply_instance

end equalizers_and_kernels

section cokernels

variables {A B C : NormedGroup.{u}}

/-- The cokernel of a morphism of normed groups. -/
@[simp]
noncomputable
def coker (f : A ⟶ B) : NormedGroup := NormedGroup.of $
  quotient_add_group.quotient f.range.topological_closure

/-- The projection onto the cokernel. -/
@[simp]
noncomputable
def coker.π {f : A ⟶ B} : B ⟶ coker f :=
normed_group_hom.normed_group.mk _

lemma coker.π_surjective {f : A ⟶ B} :
  function.surjective (coker.π : B ⟶ coker f).to_add_monoid_hom :=
surjective_quot_mk _

lemma coker.π_is_quotient {f : A ⟶ B} :
  (coker.π : B ⟶ coker f).is_quotient :=
normed_group_hom.is_quotient_quotient _

instance coker.π_epi {f : A ⟶ B} : epi (coker.π : B ⟶ coker f) :=
begin
  constructor,
  intros Z g h H,
  ext x,
  rcases coker.π_surjective x with ⟨x,rfl⟩,
  change (coker.π ≫ g) _ = _,
  rw [H],
  refl,
end

open normed_group_hom

/-- Lift (aka descend) a morphism to the cokernel. -/
noncomputable
def coker.lift {f : A ⟶ B} {g : B ⟶ C} (cond : f ≫ g = 0) : coker f ⟶ C :=
normed_group_hom.lift _ g (zero_of_closure _ _ begin
  rintros _ ⟨b,rfl⟩,
  change (f ≫ g) b = 0,
  simp [cond]
end)

@[simp]
lemma coker.lift_comp_π {f : A ⟶ B} {g : B ⟶ C} {cond : f ≫ g = 0} :
  coker.π ≫ coker.lift cond = g :=
begin
  ext,
  rw ← normed_group_hom.lift_mk f.range.topological_closure g,
  refl,
  apply zero_of_closure,
  rintro _ ⟨b,rfl⟩,
  change (f ≫ g) b = 0,
  simp [cond],
end

lemma coker.lift_unique {f : A ⟶ B} {g : B ⟶ C} {cond : f ≫ g = 0} {h : coker f ⟶ C} :
  coker.π ≫ h = g → h = coker.lift cond := lift_unique _ _ _ _

lemma coker.comp_pi_eq_zero {f : A ⟶ B} : f ≫ (coker.π : B ⟶ coker f) = 0 :=
begin
  ext a,
  rw [coe_zero, pi.zero_apply, coe_comp, coker.π, ← mem_ker, normed_group.mk.ker],
  exact subset_closure ⟨a, rfl⟩,
end

variable {D : NormedGroup.{u}}

lemma coker.lift_comp_eq_lift {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} {cond : f ≫ g = 0} :
  coker.lift cond ≫ h = coker.lift (show f ≫ (g ≫ h) = 0,
    by rw [← category_theory.category.assoc, cond, limits.zero_comp]) :=
coker.lift_unique $ by rw [← category_theory.category.assoc, coker.lift_comp_π]

lemma coker.lift_zero {f : A ⟶ B} :
  coker.lift (show f ≫ (0 : B ⟶ C) = 0, from category_theory.limits.comp_zero) = 0 :=
eq.symm $ coker.lift_unique category_theory.limits.comp_zero

/-- The downwards map between the cokernels making the diagram commute.

    A ----> B ---> coker
    |       |
    |       |
   \/      \/
    C ----> D ---> coker
 -/
noncomputable def coker.map {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D}
  (h : fab ≫ fbd = fac ≫ fcd) : coker fab ⟶ coker fcd :=
coker.lift (show fab ≫ fbd ≫ coker.π = 0, by rw [← category_theory.category.assoc, h,
  category_theory.category.assoc, coker.comp_pi_eq_zero, limits.comp_zero])

/-
If this commutes
    A ----> B ---> B'
    |       |      |
    |       |      |
   \/      \/      \/
    C ----> D ---> D'

and d^2=0 on both rows then this commutes:

coker (A → B) ----> E
   |                |
   | coker.map      |
   |                |
   \/               \/
coker (C → D) ----> F
-/

lemma coker.map_lift_comm {B' D' : NormedGroup}
  {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D}
  {h : fab ≫ fbd = fac ≫ fcd} {fbb' : B ⟶ B'} {fdd' : D ⟶ D'}
  {condb : fab ≫ fbb' = 0} {condd : fcd ≫ fdd' = 0} {g : B' ⟶ D'}
  (h' : fbb' ≫ g = fbd ≫ fdd'):
  coker.lift condb ≫ g = coker.map h ≫ coker.lift condd :=
by erw [← cancel_epi (coker.π : _ ⟶ coker fab), ← category.assoc, coker.lift_comp_π, h',
       ← category.assoc, coker.lift_comp_π, category.assoc, coker.lift_comp_π]

lemma coker.lift_comp_eq_zero {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} (cond : f ≫ g = 0)
  (cond2 : g ≫ h = 0) : coker.lift cond ≫ h = 0 :=
begin
  rw [← cancel_epi (coker.π : _ ⟶ coker f), ← category.assoc, coker.lift_comp_π],
  simp [cond2],
end

end cokernels

end NormedGroup
#lint- only unused_arguments def_lemma doc_blame
