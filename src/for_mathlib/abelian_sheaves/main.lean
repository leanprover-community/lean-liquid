import category_theory.sites.limits

import for_mathlib.abelian_sheaves.functor_category
import for_mathlib.sheaf

namespace category_theory
namespace Sheaf


noncomputable theory

universes w v u
variables {C : Type (max v u)} [category.{v} C] {J : grothendieck_topology C}
variables {A : Type w} [category.{max v u} A]

section has_zero_morphisms

variables [limits.has_zero_morphisms A]

instance : limits.has_zero_morphisms (Sheaf J A) :=
{ has_zero := λ X Y, show has_zero (X.1 ⟶ Y.1), by apply_instance,
  comp_zero' := λ X Y f Z, limits.has_zero_morphisms.comp_zero _ _,
  zero_comp' := λ X Y Z f, limits.has_zero_morphisms.zero_comp _ _ }

end has_zero_morphisms

section parallel_pair

def parallel_pair_iso {F G : Sheaf J A} (η γ : F ⟶ G) :
  limits.parallel_pair η γ ⋙ Sheaf_to_presheaf J A ≅ limits.parallel_pair η γ :=
nat_iso.of_components
(λ x,
match x with
| limits.walking_parallel_pair.zero := eq_to_iso rfl
| limits.walking_parallel_pair.one := eq_to_iso rfl
end) begin
  rintro (x|x) (y|y) (f|f|f),
  any_goals { refl },
  any_goals { ext, dsimp [parallel_pair_iso._match_1], simp },
end

end parallel_pair

section kernels

variables [limits.has_zero_morphisms A]
-- TODO: Add some instances that derive the following from `[has_kernels A]`.
variables [limits.has_limits_of_shape limits.walking_parallel_pair A]

def kernel_sheaf {F G : Sheaf J A} (η : F ⟶ G) : Sheaf J A :=
{ val := limits.kernel η,
  property := begin
    haveI : limits.has_limit (limits.parallel_pair η 0 ⋙ Sheaf_to_presheaf J A) := begin
      apply limits.has_limit_of_iso (parallel_pair_iso _ _).symm,
      apply_instance,
    end,
    let e : limits.limit (limits.parallel_pair η 0 ⋙ Sheaf_to_presheaf J A) ≅
      limits.kernel η := limits.has_limit.iso_of_nat_iso (parallel_pair_iso _ _),
    apply presheaf.is_sheaf_of_iso J e.symm,
    apply is_sheaf_of_is_limit,
    apply limits.limit.is_limit,
  end }

def kernel_ι {F G : Sheaf J A} (η : F ⟶ G) : kernel_sheaf η ⟶ F :=
limits.kernel.ι _

def kernel_fork {F G : Sheaf J A} (η : F ⟶ G) : limits.fork η 0 :=
limits.fork.of_ι (kernel_ι η) $ by { simp only [limits.comp_zero], apply limits.kernel.condition }

def is_limit_kernel_fork {F G : Sheaf J A} (η : F ⟶ G) : limits.is_limit (kernel_fork η) :=
limits.is_limit_aux _ (λ S, limits.kernel.lift _ S.ι S.condition)
begin
  intros S,
  apply limits.kernel.lift_ι,
end begin
  intros S m hm,
  ext1,
  erw hm,
  simp
end

-- Sanity check
example : limits.has_kernels (Sheaf J A) := by apply_instance

def kernel_iso_kernel_sheaf {F G : Sheaf J A} (η : F ⟶ G) :
  limits.kernel η ≅ kernel_sheaf η :=
(limits.limit.is_limit _).cone_point_unique_up_to_iso (is_limit_kernel_fork _)

@[simp]
lemma kernel_iso_kernel_sheaf_hom_ι {F G : Sheaf J A} (η : F ⟶ G) :
  (kernel_iso_kernel_sheaf η).hom ≫ kernel_ι η = limits.kernel.ι _ :=
((limits.limit.is_limit _).unique_up_to_iso (is_limit_kernel_fork η)).hom.w
  limits.walking_parallel_pair.zero

@[simp]
lemma kernel_iso_kernel_sheaf_inv_ι {F G : Sheaf J A} (η : F ⟶ G) :
  (kernel_iso_kernel_sheaf η).inv ≫ limits.kernel.ι _ = kernel_ι η :=
by simp only [← kernel_iso_kernel_sheaf_hom_ι, iso.inv_hom_id_assoc]

end kernels

end Sheaf
end category_theory
