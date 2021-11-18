import category_theory.limits.shapes.kernels
import category_theory.limits.functor_category
import category_theory.preadditive.functor_category

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

lemma nat_trans.kernel_obj_iso_hom_ι {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (nat_trans.kernel_obj_iso η X).hom ≫ kernel.ι (η.app X) = (kernel.ι η).app X :=
begin
  have h := ((limit.is_limit _).unique_up_to_iso η.is_limit_kernel_fork).hom.w
    walking_parallel_pair.zero,
  apply_fun (λ e, e.app X) at h,
  exact h
end

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

lemma nat_trans.cokernel_obj_iso_π_hom {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (cokernel.π η).app X ≫ (nat_trans.cokernel_obj_iso η X).hom = cokernel.π _ :=
begin
  have h := ((colimit.is_colimit _).unique_up_to_iso η.is_colimit_cokernel_cofork).hom.w
    walking_parallel_pair.one,
  apply_fun (λ e, e.app X) at h,
  exact h,
end

end cokernels

end category_theory
