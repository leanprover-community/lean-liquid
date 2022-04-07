import category_theory.limits.shapes.kernels
import category_theory.limits.functor_category
import category_theory.preadditive.functor_category
import category_theory.additive.basic
import category_theory.abelian.basic

import for_mathlib.abelian_of_isom_thm

namespace category_theory

universes w v u
variables {C : Type (max v u)} [category.{v} C]
variables {D : Type w} [category.{max v u} D]

open category_theory.limits

example [has_zero_morphisms D] : has_zero_morphisms (C ⥤ D) := infer_instance
example [preadditive D] : preadditive (C ⥤ D) := infer_instance

noncomputable theory

section kernels

variables [has_zero_morphisms D] [has_kernels D]

@[simps]
def nat_trans.kernel_functor {F G : C ⥤ D} (η : F ⟶ G) : C ⥤ D :=
{ obj := λ X, kernel (η.app X),
  map := λ X Y f, kernel.map _ _ (F.map f) (G.map f) (η.naturality f).symm,
  map_id' := λ X, by { ext, simp },
  map_comp' := λ X Y Z f g, by { ext, simp } }

@[simps]
def nat_trans.kernel_ι {F G : C ⥤ D} (η : F ⟶ G) :
  η.kernel_functor ⟶ F :=
{ app := λ X, kernel.ι _,
  naturality' := λ X Y f, by simp }

@[simps]
def nat_trans.kernel_fork {F G : C ⥤ D} (η : F ⟶ G) :
  kernel_fork η :=
limits.kernel_fork.of_ι η.kernel_ι $ by { ext, simp }

@[simps]
def nat_trans.is_limit_kernel_fork {F G : C ⥤ D} (η : F ⟶ G) :
  is_limit η.kernel_fork :=
is_limit_aux _ (λ S,
  { app := λ X, kernel.lift _ (S.ι.app X) $ by simp [← nat_trans.comp_app],
    naturality' := λ X Y f, by { ext, dsimp, simp } })
begin
  intros S,
  ext,
  dsimp,
  simp,
end begin
  intros S m hm,
  ext X,
  apply_fun (λ e, e.app X) at hm,
  dsimp at ⊢ hm,
  simp [hm]
end

instance functor_category_has_kernels :
  has_kernels (C ⥤ D) := ⟨λ F G η, ⟨⟨⟨_, η.is_limit_kernel_fork⟩⟩⟩⟩

def nat_trans.kernel_obj_iso {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (kernel η).obj X ≅ kernel (η.app X) :=
((limit.is_limit _).cone_point_unique_up_to_iso η.is_limit_kernel_fork).app X

@[simp, reassoc]
lemma nat_trans.kernel_obj_iso_hom_ι {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (nat_trans.kernel_obj_iso η X).hom ≫ kernel.ι (η.app X) = (kernel.ι η).app X :=
begin
  have h := ((limit.is_limit _).unique_up_to_iso η.is_limit_kernel_fork).hom.w
    walking_parallel_pair.zero,
  apply_fun (λ e, e.app X) at h,
  exact h
end

@[simp, reassoc]
lemma nat_trans.kernel_obj_iso_inv_ι {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (nat_trans.kernel_obj_iso η X).inv ≫ (kernel.ι η).app X = kernel.ι _ :=
by simp [iso.inv_comp_eq]

@[simps]
def nat_trans.cokernel_kernel_ι_iso [has_cokernels D] {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  cokernel ((kernel.ι η).app X) ≅ cokernel (kernel.ι (η.app X)) :=
{ hom := cokernel.map _ _ (nat_trans.kernel_obj_iso _ _).hom (𝟙 _) (by simp),
  inv := cokernel.map _ _ (nat_trans.kernel_obj_iso _ _).inv (𝟙 _) (by simp),
  hom_inv_id' := by { ext, dsimp, simp },
  inv_hom_id' := by { ext, dsimp, simp } }

end kernels

section cokernels

variables [has_zero_morphisms D] [has_cokernels D]

@[simps]
def nat_trans.cokernel_functor {F G : C ⥤ D} (η : F ⟶ G) : C ⥤ D :=
{ obj := λ X, cokernel (η.app X),
  map := λ X Y f, cokernel.map _ _ (F.map f) (G.map f) (η.naturality f).symm,
  map_id' := λ X, by { ext, simp },
  map_comp' := λ X Y Z f g, by { ext, simp } }

@[simps]
def nat_trans.cokernel_π {F G : C ⥤ D} (η : F ⟶ G) :
  G ⟶ η.cokernel_functor :=
{ app := λ X, cokernel.π _,
  naturality' := λ X Y f, by simp }

@[simps]
def nat_trans.cokernel_cofork {F G : C ⥤ D} (η : F ⟶ G) :
  cokernel_cofork η :=
limits.cokernel_cofork.of_π η.cokernel_π $ by { ext, simp }

@[simps]
def nat_trans.is_colimit_cokernel_cofork {F G : C ⥤ D} (η : F ⟶ G) :
  is_colimit η.cokernel_cofork :=
is_colimit_aux _ (λ S,
  { app := λ X, cokernel.desc _ (S.π.app X) $ by simp [← nat_trans.comp_app],
    naturality' := λ X Y f, by { ext, dsimp, simp } })
begin
  intros S,
  ext,
  dsimp,
  simp,
end begin
  intros S m hm,
  ext X,
  apply_fun (λ e, e.app X) at hm,
  dsimp at ⊢ hm,
  simp [hm]
end

instance functor_category_has_cokernels :
  has_cokernels (C ⥤ D) := ⟨λ F G η, ⟨⟨⟨_, η.is_colimit_cokernel_cofork⟩⟩⟩⟩

def nat_trans.cokernel_obj_iso {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (cokernel η).obj X ≅ cokernel (η.app X) :=
((colimit.is_colimit _).cocone_point_unique_up_to_iso η.is_colimit_cokernel_cofork).app X

@[simp, reassoc]
lemma nat_trans.cokernel_obj_iso_π_hom {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (cokernel.π η).app X ≫ (nat_trans.cokernel_obj_iso η X).hom = cokernel.π _ :=
begin
  have h := ((colimit.is_colimit _).unique_up_to_iso η.is_colimit_cokernel_cofork).hom.w
    walking_parallel_pair.one,
  apply_fun (λ e, e.app X) at h,
  exact h,
end

@[simp, reassoc]
lemma nat_trans.cokernel_obj_iso_π_inv {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  cokernel.π (η.app X) ≫ (nat_trans.cokernel_obj_iso η X).inv = (cokernel.π η).app X :=
by simp [iso.comp_inv_eq]

@[simps]
def nat_trans.kernel_cokernel_π_iso [has_kernels D] {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  kernel ((cokernel.π η).app X) ≅ kernel (cokernel.π (η.app X)) :=
{ hom := kernel.map _ _ (𝟙 _) (nat_trans.cokernel_obj_iso η X).hom (by simp),
  inv := kernel.map _ _ (𝟙 _) (nat_trans.cokernel_obj_iso η X).inv (by simp),
  hom_inv_id' := by { ext, dsimp, simp },
  inv_hom_id' := by { ext, dsimp, simp } }

end cokernels

section cokernels_and_kernels

variables [has_zero_morphisms D] [has_cokernels D] [has_kernels D]

lemma nat_trans.coim_to_im_app {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
 (nat_trans.cokernel_kernel_ι_iso _ _).inv ≫
 (nat_trans.cokernel_obj_iso _ _).inv ≫ (coim_to_im η).app X ≫
 (nat_trans.kernel_obj_iso _ _).hom ≫
 (nat_trans.kernel_cokernel_π_iso _ _).hom = coim_to_im (η.app X) :=
begin
  dsimp [coim_to_im],
  ext,
  dsimp [nat_trans.cokernel_obj_iso, is_colimit.cocone_point_unique_up_to_iso],
  dsimp [nat_trans.kernel_obj_iso, is_limit.cone_point_unique_up_to_iso],
  simp,
end

end cokernels_and_kernels

section additivity

variables [additive_category D]

instance : additive_category (C ⥤ D) :=
{ has_biproducts_of_shape := begin
    introsI J _ _,
    constructor,
    intros F,
    apply limits.has_biproduct.of_has_product
  end,
  -- without the infer instance, this becomes REALLY slow...
  ..(infer_instance : preadditive (C ⥤ D)) }

end additivity

section abelian

variable [abelian D]

instance additive_category_of_abelian : additive_category D :=
{ ..(infer_instance : preadditive D) } -- without the infer instance, this becomes REALLY slow...

instance abelian.is_iso_coim_to_im {X Y : D} (f : X ⟶ Y) : is_iso (coim_to_im f) :=
begin
  have : coim_to_im f = (abelian.coimage_iso_image f).hom,
  { ext,
    simp only [coim_to_im, category.assoc, abelian.image.fac, cokernel.π_desc, as_iso_hom,
      abelian.coimage_image_factorisation] },
  rw this, apply_instance,
end

instance functor_category_is_iso_coim_to_im_app {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  is_iso ((coim_to_im η).app X) :=
begin
  have : (coim_to_im η).app X =
    (nat_trans.cokernel_obj_iso _ _).hom ≫
    (nat_trans.cokernel_kernel_ι_iso _ _).hom ≫
    coim_to_im _ ≫
    (nat_trans.kernel_cokernel_π_iso _ _).inv ≫
    (nat_trans.kernel_obj_iso _ _).inv,
  { rw ← nat_trans.coim_to_im_app,
    simp only [category.assoc, iso.inv_hom_id, iso.inv_hom_id_assoc,
      iso.hom_inv_id, iso.hom_inv_id_assoc, category.comp_id] },
  rw this,
  apply is_iso.comp_is_iso,
end

instance functor_category_is_iso_coim_to_im {F G : C ⥤ D} (η : F ⟶ G) :
  is_iso (coim_to_im η) := nat_iso.is_iso_of_is_iso_app _

instance : abelian (C ⥤ D) :=
abelian_of_coim_to_im (λ F G η, infer_instance)

end abelian

end category_theory
