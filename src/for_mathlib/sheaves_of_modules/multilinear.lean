import algebra.category.Module.filtered_colimits
import algebra.category.Module.limits
import category_theory.sites.sheafification
import category_theory.sites.whiskering
import linear_algebra.pi
import linear_algebra.multilinear.basic

namespace Module

universe u
variables {R : Type u} [comm_ring R]

def product {ι : Type u} (e : ι → Module.{u} R) : Module.{u} R :=
Module.of _ $ Π i, e i

def product.π {ι : Type u} (e : ι → Module.{u} R) (i) : product e ⟶ e i :=
(linear_map.proj i : (Π j, e j) →ₗ[R] e i)

def product.lift {M : Module.{u} R} {ι : Type u} (e : ι → Module.{u} R)
  (f : Π i, M ⟶ e i) : M ⟶ product e := linear_map.pi f

@[simp]
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

variables {C : Type (max v u)} [category.{v} C] (J : grothendieck_topology C)
variables (R : Type (max v u)) [comm_ring R]

abbreviation Sheaf_of_modules := Sheaf J (Module.{max v u} R)

variables {R J}

@[simps val_obj val_map]
def Sheaf_of_modules.product {ι : Type (max v u)} (e : ι → Sheaf_of_modules J R) :
  Sheaf_of_modules J R :=
{ val :=
  { obj := λ U, Module.product (λ i, (e i).val.obj U),
    map := λ U V f, Module.product.lift _ $ λ i, Module.product.π _ i ≫ (e i).val.map f,
    map_id' := sorry,
    map_comp' := sorry },
  cond := begin
    -- Idea: The underlying presheaf is the product of the underlying presheaves of
    -- the given sheaves. The forgetful functor from sheaves to presheaves creates limits.
    sorry,
  end }

@[simps val_app]
def Sheaf_of_modules.product.π {ι : Type (max v u)} (e : ι → Sheaf_of_modules J R) (i) :
  Sheaf_of_modules.product e ⟶ e i := Sheaf.hom.mk $
{ app := λ U, Module.product.π _ _,
  naturality' := sorry }

@[simps val_app]
def Sheaf_of_modules.product.lift {M : Sheaf_of_modules J R} {ι : Type (max v u)}
  (e : ι → Sheaf_of_modules J R)
  (f : Π i, M ⟶ e i) : M ⟶ Sheaf_of_modules.product e := Sheaf.hom.mk $
{ app := λ U, Module.product.lift _ $ λ i, (f i).val.app U,
  naturality' := sorry }

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
  ext x : 3,
  apply Module.product.hom_ext,
  intros i,
  specialize h i,
  apply_fun (λ e, e.val.app x) at h,
  simpa using h
end

abbreviation Sheaf_of_modules.forget (M : Sheaf_of_modules J R) : Sheaf J (Type (max v u)) :=
(Sheaf_compose _ $ forget _).obj M

open_locale classical

structure Sheaf_of_modules.multilinear_map {ι : Type (max v u)}
  (e : ι → Sheaf_of_modules J R) (M : Sheaf_of_modules J R) :=
(η : (Sheaf_of_modules.product e).forget ⟶ M.forget)
(F : Π (U : Cᵒᵖ), multilinear_map R (λ i, (e i).val.obj U) (M.val.obj U))
(h : ∀ U, η.val.app U = F U)

end category_theory
