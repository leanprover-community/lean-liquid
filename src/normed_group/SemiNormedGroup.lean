import analysis.normed_space.normed_group_quotient

import algebra.punit_instances
import category_theory.concrete_category.bundled_hom
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.kernels
import category_theory.limits.creates

/-!
# The category of seminormed abelian groups and continuous group homomorphisms

This file in particular contains a robust API for cokernels of morphisms
of seminormed groups.

## TODO

This file would sit well in mathlib.

-/

noncomputable theory

universes u v

-- move this
section for_mathlib

-- move this, better name?
lemma norm_le_add_norm_add {V : Type*} [semi_normed_group V] (x y : V) :
  ∥x∥ ≤ ∥x + y∥ + ∥y∥ :=
calc ∥x∥ = ∥x + y - y∥ : by rw add_sub_cancel
... ≤ ∥x + y∥ + ∥y∥ : norm_sub_le _ _

end for_mathlib

open category_theory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
def SemiNormedGroup : Type (u+1) := bundled semi_normed_group

namespace SemiNormedGroup

instance bundled_hom : bundled_hom @normed_group_hom :=
⟨@normed_group_hom.to_fun, @normed_group_hom.id, @normed_group_hom.comp, @normed_group_hom.coe_inj⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] SemiNormedGroup

/-- Construct a bundled `SemiNormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [semi_normed_group M] : SemiNormedGroup := bundled.of M

instance : has_zero SemiNormedGroup := ⟨of punit⟩

instance : inhabited SemiNormedGroup := ⟨0⟩

instance (M : SemiNormedGroup) : semi_normed_group M := M.str

@[simp] lemma coe_of (V : Type u) [normed_group V] : (SemiNormedGroup.of V : Type u) = V := rfl

@[simp] lemma coe_id (V : SemiNormedGroup) : ⇑(𝟙 V) = id := rfl

instance : limits.has_zero_morphisms.{u (u+1)} SemiNormedGroup := {}

lemma iso_isometry_of_norm_noninc {V W : SemiNormedGroup} (i : V ≅ W)
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

/-- The equalizer cone for a parallel pair of morphisms of seminormed groups. -/
def parallel_pair_cone {V W : SemiNormedGroup.{u}} (f g : V ⟶ W) :
  cone (parallel_pair f g) :=
@fork.of_ι _ _ _ _ _ _ (of (f - g).ker) (normed_group_hom.incl (f - g).ker) $
begin
  ext v,
  have : v.1 ∈ (f - g).ker := v.2,
  simpa only [normed_group_hom.incl_apply, pi.zero_apply, coe_comp, normed_group_hom.coe_zero,
    subtype.val_eq_coe, normed_group_hom.mem_ker,
    normed_group_hom.coe_sub, pi.sub_apply, sub_eq_zero] using this
end

instance has_limit_parallel_pair {V W : SemiNormedGroup.{u}} (f g : V ⟶ W) :
  has_limit (parallel_pair f g) :=
{ exists_limit := nonempty.intro
  { cone := parallel_pair_cone f g,
    is_limit := fork.is_limit.mk _
      (λ c, normed_group_hom.ker.lift (fork.ι c) _ $
      show normed_group_hom.comp_hom (f - g) c.ι = 0,
      by { rw [add_monoid_hom.map_sub, add_monoid_hom.sub_apply, sub_eq_zero], exact c.condition })
      (λ c, normed_group_hom.ker.incl_comp_lift _ _ _)
      (λ c g h, by { ext x, dsimp, rw ← h, refl }) } }

instance : limits.has_equalizers.{u (u+1)} SemiNormedGroup :=
@has_equalizers_of_has_limit_parallel_pair SemiNormedGroup _ $ λ V W f g,
  SemiNormedGroup.has_limit_parallel_pair f g

instance : limits.has_kernels.{u (u+1)} SemiNormedGroup :=
by apply_instance

end equalizers_and_kernels

section cokernels

variables {A B C : SemiNormedGroup.{u}}

/-- The cokernel of a morphism of seminormed groups. -/
@[simp]
noncomputable
def coker (f : A ⟶ B) : SemiNormedGroup := SemiNormedGroup.of $
  quotient_add_group.quotient f.range

/-- The projection onto the cokernel. -/
@[simp]
noncomputable
def coker.π {f : A ⟶ B} : B ⟶ coker f :=
f.range.normed_mk

lemma coker.π_surjective {f : A ⟶ B} :
  function.surjective (coker.π : B → coker f) :=
surjective_quot_mk _

lemma coker.π_is_quotient {f : A ⟶ B} :
  add_subgroup.is_quotient (coker.π : B ⟶ coker f) :=
add_subgroup.is_quotient_quotient _

lemma coker.π_norm_noninc {f : A ⟶ B} :
  (coker.π : B ⟶ coker f).norm_noninc :=
SemiNormedGroup.coker.π_is_quotient.norm_le

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
add_subgroup.lift _ g (begin
  rintros _ ⟨b,rfl⟩,
  change (f ≫ g) b = 0,
  simp [cond]
end)

@[simp]
lemma coker.lift_comp_π {f : A ⟶ B} {g : B ⟶ C} {cond : f ≫ g = 0} :
  coker.π ≫ coker.lift cond = g :=
begin
  ext,
  rw ← f.range.lift_mk g,
  refl,
  rintro _ ⟨b,rfl⟩,
  change (f ≫ g) b = 0,
  simp [cond],
end

@[simp]
lemma coker.lift_comp_π_apply {f : A ⟶ B} {g : B ⟶ C} {cond : f ≫ g = 0} (x : B) :
  coker.lift cond (coker.π x) = g x :=
show (coker.π ≫ coker.lift cond) x = g x, by rw coker.lift_comp_π

lemma coker.lift_unique {f : A ⟶ B} {g : B ⟶ C} {cond : f ≫ g = 0} {h : coker f ⟶ C} :
  coker.π ≫ h = g → h = coker.lift cond := add_subgroup.lift_unique _ _ _ _

lemma coker.comp_pi_eq_zero {f : A ⟶ B} : f ≫ (coker.π : B ⟶ coker f) = 0 :=
begin
  ext a,
  rw [coe_zero, pi.zero_apply, coe_comp, coker.π, ← mem_ker, f.range.ker_normed_mk],
  exact set.mem_range_self a
end

@[simp]
lemma coker.pi_apply_dom_eq_zero {f : A ⟶ B} (x : A) : (coker.π : B ⟶ coker f) (f x) = 0 :=
show (f ≫ (coker.π : B ⟶ coker f)) x = 0, by { rw [coker.comp_pi_eq_zero], refl }

variable {D : SemiNormedGroup.{u}}

lemma coker.lift_comp_eq_lift {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} {cond : f ≫ g = 0} :
  coker.lift cond ≫ h = coker.lift (show f ≫ (g ≫ h) = 0,
    by rw [← category_theory.category.assoc, cond, limits.zero_comp]) :=
coker.lift_unique $ by rw [← category_theory.category.assoc, coker.lift_comp_π]

lemma coker.lift_zero {f : A ⟶ B} :
  coker.lift (show f ≫ (0 : B ⟶ C) = 0, from category_theory.limits.comp_zero) = 0 :=
eq.symm $ coker.lift_unique category_theory.limits.comp_zero

section
open_locale nnreal

-- maybe prove this for `normed_group_hom` first, without the category lib
lemma coker.lift_bound_by {f : A ⟶ B} {g : B ⟶ C} {cond : f ≫ g = 0} {c : ℝ≥0}
  (hg : g.bound_by c) :
  (coker.lift cond).bound_by c :=
begin
  intros x,
  by_cases hc : c = 0,
  { simp only [hc, nnreal.coe_zero, zero_mul] at hg ⊢,
    obtain ⟨x, rfl⟩ := coker.π_surjective x,
    show ∥g x∥ ≤ 0,
    calc ∥g x∥ ≤ 0 * ∥x∥ : hg x
    ... = 0 : zero_mul _ },
  { replace hc : 0 < c := pos_iff_ne_zero.mpr hc,
    apply le_of_forall_pos_le_add,
    intros ε hε,
    have aux : 0 < (ε / c) := div_pos hε hc,
    obtain ⟨x, rfl, Hx⟩ : ∃ x', coker.π x' = x ∧ ∥x'∥ < ∥x∥ + (ε / c) :=
      coker.π_is_quotient.norm_lift aux _,
    rw coker.lift_comp_π_apply,
    calc ∥g x∥ ≤ c * ∥x∥ : hg x
    ... ≤ c * (∥coker.π x∥ + ε / c) : (mul_le_mul_left _).mpr Hx.le
    ... = c * _ + ε : _,
    { exact_mod_cast hc },
    { rw [mul_add, mul_div_cancel'], exact_mod_cast hc.ne' } },
end

-- maybe prove this for `normed_group_hom` first, without the category lib
lemma coker.lift_norm_noninc {f : A ⟶ B} {g : B ⟶ C} {cond : f ≫ g = 0}
  (hg : g.norm_noninc) :
  (coker.lift cond).norm_noninc :=
λ x, by simpa only [one_mul, nnreal.coe_one] using coker.lift_bound_by hg.bound_by_one x

end

-- maybe prove this for `normed_group_hom` first, without the category lib
lemma neg_norm_noninc (f : A ⟶ B) (hf : f.norm_noninc) : (-f).norm_noninc :=
λ x, (norm_neg (f x)).le.trans (hf x)

-- The next two declarations are available for any category with cokernels in #7623
-- as `cokernel.map` and `cokernel.map_desc`.

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

coker (A → B) ----> B'
   |                |
   | coker.map      |
   |                |
   \/               \/
coker (C → D) ----> D'
-/

lemma coker.map_lift_comm {B' D' : SemiNormedGroup}
  {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D}
  {h : fab ≫ fbd = fac ≫ fcd} {fbb' : B ⟶ B'} {fdd' : D ⟶ D'}
  {condb : fab ≫ fbb' = 0} {condd : fcd ≫ fdd' = 0} {g : B' ⟶ D'}
  (h' : fbb' ≫ g = fbd ≫ fdd'):
  coker.lift condb ≫ g = coker.map h ≫ coker.lift condd :=
begin
  delta coker.map,
  simp only [← cancel_epi (coker.π : _ ⟶ coker fab), ← category.assoc, coker.lift_comp_π, h'],
  rw [category.assoc, coker.lift_comp_π]
end

lemma coker.lift_comp_eq_zero {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} (cond : f ≫ g = 0)
  (cond2 : g ≫ h = 0) : coker.lift cond ≫ h = 0 :=
begin
  rw [← cancel_epi (coker.π : _ ⟶ coker f), ← category.assoc, coker.lift_comp_π],
  simp [cond2],
end

end cokernels

end SemiNormedGroup
#lint- only unused_arguments def_lemma doc_blame
