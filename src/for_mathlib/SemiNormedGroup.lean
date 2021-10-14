import analysis.normed.group.SemiNormedGroup
import analysis.normed.group.SemiNormedGroup.kernels
import analysis.normed.group.quotient

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

open category_theory

namespace SemiNormedGroup

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

open normed_group_hom

variable {D : SemiNormedGroup.{u}}

-- The next two declarations are available for any category with cokernels in #7623
-- as `cokernel.map` and `cokernel.map_desc`.

/-- The downwards map between the cokernels making the diagram commute.

    A ----> B ---> coker
    |       |
    |       |
   \/      \/
    C ----> D ---> coker
 -/
noncomputable def explicit_coker.map {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D}
  (h : fab ≫ fbd = fac ≫ fcd) : explicit_cokernel fab ⟶ explicit_cokernel fcd :=
@explicit_cokernel_desc _ _ _ fab (fbd ≫ explicit_cokernel_π _) $ by simp [reassoc_of h]

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

lemma explicit_coker.map_lift_comm {B' D' : SemiNormedGroup}
  {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D}
  {h : fab ≫ fbd = fac ≫ fcd} {fbb' : B ⟶ B'} {fdd' : D ⟶ D'}
  {condb : fab ≫ fbb' = 0} {condd : fcd ≫ fdd' = 0} {g : B' ⟶ D'}
  (h' : fbb' ≫ g = fbd ≫ fdd'):
  explicit_cokernel_desc condb ≫ g = explicit_coker.map h ≫ explicit_cokernel_desc condd :=
begin
  delta explicit_coker.map,
  simp [← cancel_epi (explicit_cokernel_π fab), category.assoc, explicit_cokernel_π_desc, h']
end

end cokernels

end SemiNormedGroup
#lint- only unused_arguments def_lemma doc_blame
