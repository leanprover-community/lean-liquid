import algebra.category.Module.filtered_colimits
import algebra.category.Module.limits
import category_theory.sites.sheafification
import category_theory.sites.whiskering
import linear_algebra.pi
import linear_algebra.multilinear.basic

open_locale classical

namespace Module

universe u
variables {R : Type u} [comm_ring R]

def product {ι : Type u} (e : ι → Module.{u} R) : Module.{u} R :=
Module.of _ $ Π i, e i

def product.π {ι : Type u} (e : ι → Module.{u} R) (i) : product e ⟶ e i :=
(linear_map.proj i : (Π j, e j) →ₗ[R] e i)

def product.lift {M : Module.{u} R} {ι : Type u} (e : ι → Module.{u} R)
  (f : Π i, M ⟶ e i) : M ⟶ product e := linear_map.pi f

@[simp, reassoc, elementwise]
lemma product.lift_π {M : Module.{u} R} {ι : Type u} (e : ι → Module.{u} R)
  (f : Π i, M ⟶ e i) (i) : product.lift e f ≫ product.π e i = f i := by { ext, refl }

lemma product.hom_ext {M : Module.{u} R} {ι : Type u} (e : ι → Module.{u} R)
  (f g : M ⟶ product e) (h : ∀ i, f ≫ product.π e i = g ≫ product.π e i) : f = g :=
begin
  ext m i,
  specialize h i,
  apply_fun (λ e, e m) at h,
  exact h
end

end Module

namespace category_theory

universes w v u

variables (C : Type (max v u)) [category.{v} C] (J : grothendieck_topology C)
variables (R : Type (max v u)) [comm_ring R]

abbreviation functor_of_modules := C ⥤ Module.{max v u} R

variable {C}

abbreviation Sheaf_of_modules := Sheaf J (Module.{max v u} R)

variables {R J}

@[simps]
def functor_of_modules.product {ι : Type (max v u)} (e : ι → functor_of_modules C R) :
  functor_of_modules C R :=
{ obj := λ U, Module.product (λ i, (e i).obj U),
  map := λ U V f, Module.product.lift _ $ λ i, Module.product.π _ i ≫ (e i).map f }

@[simps]
def functor_of_modules.product.π {ι : Type (max v u)} (e : ι → functor_of_modules C R) (i) :
  functor_of_modules.product e ⟶ e i :=
{ app := λ U, Module.product.π _ _ }

@[simps]
def functor_of_modules.product.lift {M : functor_of_modules C R} {ι : Type (max v u)}
  (e : ι → functor_of_modules C R)
  (f : Π i, M ⟶ e i) : M ⟶ functor_of_modules.product e :=
{ app := λ U, Module.product.lift _ $ λ i, (f i).app U,
  naturality' := begin
    intros U V f,
    apply Module.product.hom_ext,
    intros i,
    simp,
  end }

@[simp, reassoc]
lemma functor_of_modules.product.lift_π {M : functor_of_modules C R} {ι : Type (max v u)}
  (e : ι → functor_of_modules C R)
  (f : Π i, M ⟶ e i) (i) :
  functor_of_modules.product.lift e f ≫ functor_of_modules.product.π e i = f i :=
by { ext : 2, dsimp, simp }

lemma functor_of_modules.product.hom_ext {M : functor_of_modules C R} {ι : Type (max v u)}
  (e : ι → functor_of_modules C R) (f g : M ⟶ functor_of_modules.product e)
  (h : ∀ i, f ≫ functor_of_modules.product.π e i = g ≫ functor_of_modules.product.π e i) :
  f = g :=
begin
  ext x : 2,
  apply Module.product.hom_ext,
  intros i,
  specialize h i,
  apply_fun (λ e, e.app x) at h,
  simpa using h,
end

structure functor_of_modules.multilinear_map {ι : Type (max v u)}
  (e : ι → functor_of_modules C R) (M : functor_of_modules C R) :=
(η : functor_of_modules.product e ⋙ forget _ ⟶ M ⋙ forget _)
(F : Π U : C, multilinear_map R (λ i, (e i).obj U) (M.obj U))
(h : ∀ U, η.app U = F U)

@[simps val_obj val_map]
def Sheaf_of_modules.product {ι : Type (max v u)} (e : ι → Sheaf_of_modules J R) :
  Sheaf_of_modules J R :=
{ val := functor_of_modules.product (λ i, (e i).val),
  cond := begin
    -- Idea: The underlying presheaf is the product of the underlying presheaves of
    -- the given sheaves. The forgetful functor from sheaves to presheaves creates limits.
    sorry,
  end }

@[simps val_app]
def Sheaf_of_modules.product.π {ι : Type (max v u)} (e : ι → Sheaf_of_modules J R) (i) :
  Sheaf_of_modules.product e ⟶ e i :=
⟨functor_of_modules.product.π _ _⟩

@[simps val_app]
def Sheaf_of_modules.product.lift {M : Sheaf_of_modules J R} {ι : Type (max v u)}
  (e : ι → Sheaf_of_modules J R)
  (f : Π i, M ⟶ e i) : M ⟶ Sheaf_of_modules.product e :=
⟨functor_of_modules.product.lift _ $ λ i, (f i).val⟩

@[simp]
lemma Sheaf_of_modules.product.lift_π {M : Sheaf_of_modules J R} {ι : Type (max v u)}
  (e : ι → Sheaf_of_modules J R)
  (f : Π i, M ⟶ e i) (i) :
  Sheaf_of_modules.product.lift e f ≫ Sheaf_of_modules.product.π e i = f i :=
by { ext, simp }

lemma Sheaf_of_modules.product.hom_ext {M : Sheaf_of_modules J R} {ι : Type (max v u)}
  (e : ι → Sheaf_of_modules J R) (f g : M ⟶ Sheaf_of_modules.product e)
  (h : ∀ i, f ≫ Sheaf_of_modules.product.π _ i = g ≫ Sheaf_of_modules.product.π _ i) : f = g :=
begin
  ext1,
  apply functor_of_modules.product.hom_ext,
  intros i,
  specialize h i,
  apply_fun (λ e, e.val) at h,
  exact h
end

abbreviation Sheaf_of_modules.forget (M : Sheaf_of_modules J R) : Sheaf J (Type (max v u)) :=
(Sheaf_compose _ $ forget _).obj M

structure Sheaf_of_modules.multilinear_map {ι : Type (max v u)}
  (e : ι → Sheaf_of_modules J R) (M : Sheaf_of_modules J R) :=
(η : functor_of_modules.multilinear_map (λ i, (e i).val) M.val)

end category_theory
