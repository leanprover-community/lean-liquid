import category_theory.sites.limits

import for_mathlib.abelian_sheaves.functor_category
import for_mathlib.sheaf
import for_mathlib.abelian_sheaves.left_exact

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
{ val := limits.kernel ((Sheaf_to_presheaf J A).map η),
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

section kernels_and_cokernels

variables [limits.has_zero_morphisms A]
-- TODO: use has kernels and cokernels, when possible... see above
variables [limits.has_colimits_of_shape limits.walking_parallel_pair A]
variables [limits.has_limits_of_shape limits.walking_parallel_pair A]

-- We will need to sheafify....
variables [concrete_category.{max v u} A]
variables [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.cover X), limits.has_multiequalizer (S.index P)]
variables [limits.preserves_limits (forget A)]
variables [∀ (X : C), limits.has_colimits_of_shape (J.cover X)ᵒᵖ A]
variables [∀ (X : C), limits.preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget A)]
variables [reflects_isomorphisms (forget A)]

def coim_to_im'_aux {F G : Sheaf J A} (η : F ⟶ G) :
coim ((Sheaf_to_presheaf J A).map η) ⟶ (Sheaf_to_presheaf J A).obj (kernel_sheaf (cokernel_π η)) :=
(coim_to_im _ ≫ limits.kernel.lift _ (limits.kernel.ι _) begin
  dsimp [cokernel_π],
  rw [← category.assoc, limits.kernel.condition],
  simp,
end)

def coim_to_im' {F G : Sheaf J A} (η : F ⟶ G) :
  cokernel_sheaf (kernel_ι η) ⟶ kernel_sheaf (cokernel_π η) :=
J.sheafify_lift (coim_to_im'_aux η) (kernel_sheaf _).2

def kernel_sheaf_cokernel_π_iso {F G : Sheaf J A} (η : F ⟶ G) :
  kernel_sheaf (limits.cokernel.π η) ≅ kernel_sheaf (cokernel_π η) :=
{ hom := limits.kernel.map _ _ (𝟙 _)
    ((Sheaf_to_presheaf J A).map (cokernel_iso_cokernel_sheaf η).hom) begin
      rw ← functor.map_comp,
      dsimp [cokernel_iso_cokernel_sheaf, limits.is_colimit.cocone_point_unique_up_to_iso,
        cokernel_cofork],
      simp,
    end,
  inv := limits.kernel.map _ _ (𝟙 _)
    ((Sheaf_to_presheaf J A).map (cokernel_iso_cokernel_sheaf η).inv) begin
      rw ← functor.map_comp,
      dsimp [cokernel_iso_cokernel_sheaf, limits.is_colimit.cocone_point_unique_up_to_iso,
        cokernel_π, is_colimit_cokernel_cofork, limits.is_colimit_aux],
      erw [category.id_comp, category.assoc, J.to_sheafify_sheafify_lift,
        limits.cokernel.π_desc],
    end,
  hom_inv_id' := begin
    ext1,
    dsimp,
    delta limits.kernel.map,
    conv_rhs { erw category.id_comp },
    erw [category.assoc, limits.kernel.lift_ι, ← category.assoc, limits.kernel.lift_ι,
      category.comp_id, category.comp_id],
  end,
  inv_hom_id' := begin
    ext1,
    dsimp,
    delta limits.kernel.map,
    conv_rhs { erw category.id_comp },
    erw [category.assoc, limits.kernel.lift_ι, ← category.assoc, limits.kernel.lift_ι,
      category.comp_id, category.comp_id],
  end }

def cokernel_sheaf_kernel_ι_iso {F G : Sheaf J A} (η : F ⟶ G) :
  cokernel_sheaf (limits.kernel.ι η) ≅ cokernel_sheaf (kernel_ι η) :=
{ hom := J.sheafify_lift
    (limits.cokernel.map _ _ ((Sheaf_to_presheaf J A).map (kernel_iso_kernel_sheaf η).hom) (𝟙 _)
      (by rw [category.comp_id, ← functor.map_comp, kernel_iso_kernel_sheaf_hom_ι])
      ≫ J.to_sheafify _) (cokernel_sheaf _).2,
  inv := J.sheafify_lift
    (limits.cokernel.map _ _ ((Sheaf_to_presheaf J A).map (kernel_iso_kernel_sheaf η).inv) (𝟙 _)
      (by rw [category.comp_id, ← functor.map_comp, kernel_iso_kernel_sheaf_inv_ι])
      ≫ J.to_sheafify _)
    (cokernel_sheaf _).2,
  hom_inv_id' := begin
    apply J.sheafify_hom_ext _ _ (cokernel_sheaf _).2,
    erw [← category.assoc, J.to_sheafify_sheafify_lift, category.assoc,
      J.to_sheafify_sheafify_lift, ← category.assoc],
    conv_rhs { erw category.comp_id },
    convert category.id_comp _,
    ext1,
    delta limits.cokernel.map,
    erw [← category.assoc, limits.coequalizer.π_desc, category.id_comp,
      limits.coequalizer.π_desc, category.id_comp, category.comp_id],
  end,
  inv_hom_id' := begin
    apply J.sheafify_hom_ext _ _ (cokernel_sheaf _).2,
    erw [← category.assoc, J.to_sheafify_sheafify_lift, category.assoc,
      J.to_sheafify_sheafify_lift, ← category.assoc],
    conv_rhs { erw category.comp_id },
    convert category.id_comp _,
    ext1,
    delta limits.cokernel.map,
    erw [← category.assoc, limits.coequalizer.π_desc, category.id_comp,
      limits.coequalizer.π_desc, category.id_comp, category.comp_id],
  end }

lemma eq_coim_to_im' {F G : Sheaf J A} (η : F ⟶ G) :
  (cokernel_sheaf_kernel_ι_iso η).inv ≫
  (cokernel_iso_cokernel_sheaf _).inv ≫
  coim_to_im η  ≫
  (kernel_iso_kernel_sheaf _).hom ≫
  (kernel_sheaf_cokernel_π_iso η).hom
  = coim_to_im' η :=
begin
  dsimp [coim_to_im, cokernel_sheaf_kernel_ι_iso,
    coim_to_im', coim_to_im'_aux, kernel_sheaf_cokernel_π_iso,
    limits.is_colimit.cocone_point_unique_up_to_iso,
    limits.is_limit.cone_point_unique_up_to_iso],
  delta limits.kernel.map limits.cokernel.map,
  apply J.sheafify_lift_unique,
  ext : 2,
  conv_rhs {
    erw [← category.assoc, limits.cokernel.π_desc,
      category.assoc, limits.kernel.lift_ι, limits.kernel.lift_ι] },
  simp only [category.assoc],
  iterate 4 { erw category.assoc _ _
    (limits.equalizer.ι ((Sheaf_to_presheaf J A).map (cokernel_π η)) _) },
  erw [limits.kernel.lift_ι],
  erw [← category.assoc _ _ (𝟙 G.1), kernel_iso_kernel_sheaf_hom_ι],
  erw [← category.assoc _ _ (𝟙 G.1), ← category.assoc (J.to_sheafify _),
    J.to_sheafify_sheafify_lift, ← category.assoc (limits.cokernel.π _),
    ← category.assoc (limits.cokernel.π _),
    limits.cokernel.π_desc, category.id_comp, category.comp_id],
  dsimp [cokernel_iso_cokernel_sheaf,
    limits.is_colimit.cocone_point_unique_up_to_iso,
    is_colimit_cokernel_cofork, limits.is_colimit_aux],
  rw [category.assoc, ← category.assoc (J.to_sheafify _),
    J.to_sheafify_sheafify_lift],
  simp only [← category.assoc, limits.cokernel.π_desc],
  erw [limits.cokernel.π_desc (limits.kernel.ι η),
    limits.kernel.lift_ι (limits.cokernel.π η)],
end

lemma coim_to_im_eq {F G : Sheaf J A} (η : F ⟶ G) :
  coim_to_im η =
  (cokernel_iso_cokernel_sheaf _).hom ≫
  (cokernel_sheaf_kernel_ι_iso η).hom ≫
  coim_to_im' η ≫
  (kernel_sheaf_cokernel_π_iso η).inv ≫
  (kernel_iso_kernel_sheaf _).inv
  :=
begin
  rw ← eq_coim_to_im',
  simp only [category.assoc, iso.hom_inv_id, iso.inv_hom_id,
    iso.hom_inv_id_assoc, iso.inv_hom_id_assoc, category.comp_id],
end

end kernels_and_cokernels

section preadditive

variable [preadditive A]

instance : preadditive (Sheaf J A) :=
{ hom_group := λ P Q, show (add_comm_group (P.1 ⟶ Q.1)), by apply_instance,
  add_comp' := λ P Q R f g h, preadditive.add_comp _ _ _ _ _ _,
  comp_add' := λ P Q R f g h, preadditive.comp_add _ _ _ _ _ _ }

end preadditive

section additive

variable [additive_category A]

instance : additive_category (Sheaf J A) :=
{ has_biproducts_of_shape := begin
    introsI J _ _,
    constructor,
    intros F,
    apply limits.has_biproduct.of_has_product
  end,
  ..(by apply_instance : preadditive (Sheaf J A)) }

end additive

section abelian

variables [abelian A]
-- We need sheafification
variables [concrete_category.{max v u} A]
variables [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.cover X), limits.has_multiequalizer (S.index P)]
variables [limits.preserves_limits (forget A)]
variables [∀ (X : C), limits.has_colimits_of_shape (J.cover X)ᵒᵖ A]
variables [∀ (X : C), limits.preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget A)]
variables [reflects_isomorphisms (forget A)]

open grothendieck_topology

def parallel_pair_sheafification {F G : Sheaf J A} (η : F ⟶ G) : limits.parallel_pair
  (limits.cokernel.π ((Sheaf_to_presheaf J A).map η)) 0 ⋙ J.sheafification A ≅
  limits.parallel_pair (cokernel_π η) 0 :=
nat_iso.of_components
(λ x,
match x with
| limits.walking_parallel_pair.zero := by { dsimp, refine (J.iso_sheafify G.2).symm }
| limits.walking_parallel_pair.one := by { dsimp, exact eq_to_iso rfl }
end)
begin
  -- This proof is SLOW :-(
  rintros (a|a) (b|b) (f|f|f),
  { dsimp [parallel_pair_sheafification._match_1],
    simp only [iso.eq_inv_comp, functor.map_id],
    dsimp [grothendieck_topology.iso_sheafify],
    rw [← category.assoc, is_iso.comp_inv_eq, category.id_comp],
    change J.to_sheafify _ ≫ (sheafification J A).map _ = _,
    erw [functor.map_id, category.comp_id] },
  { dsimp [parallel_pair_sheafification._match_1],
    rw [category.comp_id, iso.eq_inv_comp],
    dsimp [grothendieck_topology.iso_sheafify, cokernel_π],
    change (to_sheafification J A).app _ ≫ (sheafification J A).map _ = _,
    rw ← (to_sheafification J A).naturality,
    refl },
  { dsimp [parallel_pair_sheafification._match_1],
    simp only [limits.comp_zero, category.comp_id],
    change (sheafification J A).map _ = _,
    apply J.sheafify_hom_ext,
    { exact plus.is_sheaf_plus_plus J (limits.cokernel η) },
    erw ← (to_sheafification J A).naturality,
    simp },
  { dsimp [parallel_pair_sheafification._match_1],
    simp only [limits.comp_zero, category.id_comp, category.comp_id],
    change (sheafification J A).map _ = _,
    simp only [functor.map_id],
    erw (sheafification J A).map_id, refl },
end .

def kernel_cokernel_π_iso {F G : Sheaf J A} (η : F ⟶ G) :
  J.sheafify (limits.kernel (limits.cokernel.π ((Sheaf_to_presheaf J A).map η))) ≅
  limits.kernel ((Sheaf_to_presheaf J A).map (cokernel_π η)) :=
begin
  let e := (limits.is_limit_of_preserves (sheafification J A) (limits.limit.is_limit
      (limits.parallel_pair (limits.cokernel.π
      ((Sheaf_to_presheaf J A).map η)) 0))).cone_point_unique_up_to_iso (limits.limit.is_limit _),
  refine e ≪≫ _,
  change limits.limit _ ≅ _,
  refine limits.has_limit.iso_of_nat_iso _,
  apply parallel_pair_sheafification,
end

/-
{ hom := J.sheafify_lift (limits.kernel.map _ _ (𝟙 _) (J.to_sheafify _) sorry) sorry,
  inv := begin
    let e : J.sheafify ((Sheaf_to_presheaf J A).obj G) ⟶
      J.sheafify (limits.cokernel ((Sheaf_to_presheaf J A).map η)) :=
        (sheafification J A).map (limits.cokernel.π _),
    let ee : limits.kernel ((Sheaf_to_presheaf J A).map (cokernel_π η)) ⟶ limits.kernel e,
    { refine limits.kernel.map _ _ (J.to_sheafify _) (𝟙 _) _,
      rw category.comp_id,
      dsimp only [e],
      rw ← grothendieck_topology.to_sheafification_app,
      rw ← (to_sheafification J A).naturality,
      refl },
    refine ee ≫ _,
    dsimp only [e],
    change limits.kernel ((Sheaf_to_presheaf J A).map ((presheaf_to_Sheaf J A).map _)) ⟶ _,
    refine (Sheaf_to_presheaf J A).map (kernel_iso_kernel_sheaf _).inv ≫ _,
    change _ ⟶ (Sheaf_to_presheaf J A).obj ((presheaf_to_Sheaf J A).obj _),
    refine (Sheaf_to_presheaf J A).map _,
    haveI : is_left_adjoint (presheaf_to_Sheaf J A) := sorry,
    -- Now we need to use the fact that finite limits commute with sheafification,
    -- i.e. that sheafification is left exact.
    sorry
  end,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }
-/

lemma coim_to_im'_eq {F G : Sheaf J A} (η : F ⟶ G) :
  (Sheaf_to_presheaf J A).map (coim_to_im' η) =
  (sheafification J A).map (coim_to_im _) ≫ (kernel_cokernel_π_iso η).hom :=
begin
  sorry
end

instance is_iso_coim_to_im {F G : Sheaf J A} (η : F ⟶ G) : is_iso (coim_to_im η) :=
begin
  rw coim_to_im_eq,
  suffices : is_iso (coim_to_im' η),
  { resetI, apply is_iso.comp_is_iso },
  suffices : is_iso ((Sheaf_to_presheaf J A).map (coim_to_im' η)),
  { resetI, apply is_iso_of_fully_faithful (Sheaf_to_presheaf J A) },
  rw coim_to_im'_eq,
  apply is_iso.comp_is_iso,
end

instance abelian : abelian (Sheaf J A) :=
abelian_of_coim_to_im (λ F G η, infer_instance)

end abelian

end Sheaf
end category_theory
