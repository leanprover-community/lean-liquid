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

section cokernels

variables [limits.has_zero_morphisms A]
-- TODO: Add some instances that derive the following from `[has_cokernels A]`.
variables [limits.has_colimits_of_shape limits.walking_parallel_pair A]

-- We will need to sheafify....
variables [concrete_category.{max v u} A]
variables [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.cover X), limits.has_multiequalizer (S.index P)]
variables [limits.preserves_limits (forget A)]
variables [∀ (X : C), limits.has_colimits_of_shape (J.cover X)ᵒᵖ A]
variables [∀ (X : C), limits.preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget A)]
variables [reflects_isomorphisms (forget A)]

def cokernel_sheaf {F G : Sheaf J A} (η : F ⟶ G) : Sheaf J A :=
{ val := J.sheafify (limits.cokernel ((Sheaf_to_presheaf J A).map η)), -- ;-)
  property := grothendieck_topology.plus.is_sheaf_plus_plus _ _ }

def cokernel_π {F G : Sheaf J A} (η : F ⟶ G) : G ⟶ cokernel_sheaf η :=
show (Sheaf_to_presheaf J A).obj G ⟶ J.sheafify (limits.cokernel ((Sheaf_to_presheaf J A).map η)),
from limits.cokernel.π ((Sheaf_to_presheaf J A).map η) ≫
  J.to_sheafify (limits.cokernel ((Sheaf_to_presheaf J A).map η))

def cokernel_cofork {F G : Sheaf J A} (η : F ⟶ G) : limits.cofork η 0 :=
limits.cofork.of_π (cokernel_π η) begin
  dsimp only [cokernel_π],
  erw [← category.assoc, limits.cokernel.condition],
  simp,
end

def is_colimit_cokernel_cofork {F G : Sheaf J A} (η : F ⟶ G) :
  limits.is_colimit (cokernel_cofork η) :=
limits.is_colimit_aux _ (λ S,
  J.sheafify_lift (limits.cokernel.desc ((Sheaf_to_presheaf J A).map η) S.π S.condition) (S.X.2))
begin
  intros S,
  change (_ ≫ _) ≫ _ = _,
  rw [category.assoc, J.to_sheafify_sheafify_lift, limits.cokernel.π_desc],
end begin
  intros S m hm,
  apply J.sheafify_lift_unique,
  change (_ ≫ _) ≫ _ = _ at hm,
  rw category.assoc at hm,
  ext1,
  rw [hm, limits.cokernel.π_desc],
end

-- Sanity check
example : limits.has_cokernels (Sheaf J A) := by apply_instance

def cokernel_iso_cokernel_sheaf {F G : Sheaf J A} (η : F ⟶ G) :
  limits.cokernel η ≅ cokernel_sheaf η :=
(limits.colimit.is_colimit _).cocone_point_unique_up_to_iso (is_colimit_cokernel_cofork _)

@[simp]
lemma cokernel_iso_cokernel_sheaf_hom_π {F G : Sheaf J A} (η : F ⟶ G) :
  limits.cokernel.π η ≫ (cokernel_iso_cokernel_sheaf η).hom = cokernel_π _ :=
((limits.colimit.is_colimit _).unique_up_to_iso (is_colimit_cokernel_cofork η)).hom.w
  limits.walking_parallel_pair.one

@[simp]
lemma cokernel_iso_cokernel_sheaf_inv_π {F G : Sheaf J A} (η : F ⟶ G) :
  cokernel_π η ≫ (cokernel_iso_cokernel_sheaf η).inv = limits.cokernel.π η :=
by simp only [← cokernel_iso_cokernel_sheaf_hom_π,
  category.assoc, iso.hom_inv_id, category.comp_id]

end cokernels

end Sheaf
end category_theory
