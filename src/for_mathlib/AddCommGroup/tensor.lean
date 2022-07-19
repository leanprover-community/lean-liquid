
import linear_algebra.tensor_product

import for_mathlib.AddCommGroup_instances
import for_mathlib.AddCommGroup.explicit_products
import for_mathlib.AddCommGroup.ab4
import for_mathlib.AddCommGroup
import for_mathlib.exact_filtered_colimits
import for_mathlib.split_exact
import for_mathlib.ab4
import for_mathlib.ab52
import category_theory.limits.preserves.limits

noncomputable theory

universes u
open_locale tensor_product

open category_theory

namespace AddCommGroup

def linear_equiv_to_iso {A B : AddCommGroup.{u}}
  (e : A ≃ₗ[ℤ] B) :
  A ≅ B :=
{ hom := e.to_linear_map.to_add_monoid_hom,
  inv := e.symm.to_linear_map.to_add_monoid_hom,
  hom_inv_id' := begin
    ext t,
    simp,
  end,
  inv_hom_id' := begin
    ext t,
    simp,
  end }

def tensor (A B : AddCommGroup.{u}) : AddCommGroup.{u} :=
AddCommGroup.of (A ⊗[ℤ] B)

lemma tensor_ext {A B C : AddCommGroup.{u}} (f g : A.tensor B ⟶ C)
  (h : ∀ x y, f (x ⊗ₜ y) = g (x ⊗ₜ y)) : f = g :=
begin
  ext1 x, show f.to_int_linear_map x = g.to_int_linear_map x, congr' 1, clear x,
  apply tensor_product.ext', exact h,
end

def tensor_uncurry {A B C : AddCommGroup.{u}}
  (e : A ⟶ AddCommGroup.of (B ⟶ C)) : tensor A B ⟶ C :=
linear_map.to_add_monoid_hom $ tensor_product.lift $
let e' := e.to_int_linear_map,
  e'' : (B ⟶ C) →ₗ[ℤ] (B →ₗ[ℤ] C) :=
  add_monoid_hom.to_int_linear_map
  { to_fun := λ f, f.to_int_linear_map,
    map_zero' := by { ext, refl },
    map_add' := λ f g, by { ext, refl } } in
e''.comp e'

def tensor_curry {A B C : AddCommGroup.{u}}
  (e : tensor A B ⟶ C) : A ⟶ AddCommGroup.of (B ⟶ C) :=
{ to_fun := λ a,
  { to_fun := λ b, e (a ⊗ₜ b),
    map_zero' := by { rw [tensor_product.tmul_zero, e.map_zero], },
    map_add' := begin
      intros b c,
      rw [tensor_product.tmul_add, e.map_add],
    end },
  map_zero' := begin
    ext t,
    dsimp,
    rw [tensor_product.zero_tmul, e.map_zero],
  end,
  map_add' := begin
    intros x y, ext t,
    dsimp,
    rw [tensor_product.add_tmul, e.map_add],
  end }

.

@[simps]
def tensor_curry_equiv (A B C : AddCommGroup.{u}) :
  (tensor A B ⟶ C) ≃+ (A ⟶ (AddCommGroup.of (B ⟶ C))) :=
{ to_fun := tensor_curry,
  inv_fun := tensor_uncurry,
  left_inv := begin
    intros f, apply tensor_ext, intros x y, dsimp only [tensor_uncurry, tensor_curry],
    erw [tensor_product.lift.tmul], refl,
  end,
  right_inv := λ f, by { ext, dsimp only [tensor_uncurry, tensor_curry],
    erw [tensor_product.lift.tmul], refl, },
  map_add' := λ x y, by { ext, refl } }

.

@[simp]
lemma tensor_curry_uncurry {A B C : AddCommGroup.{u}}
  (e : A ⟶ (AddCommGroup.of (B ⟶ C))) :
  tensor_curry (tensor_uncurry e) = e :=
(tensor_curry_equiv A B C).apply_symm_apply e

@[simp]
lemma tensor_uncurry_curry {A B C : AddCommGroup.{u}}
  (e : tensor A B ⟶ C) :
  tensor_uncurry (tensor_curry e) = e :=
(tensor_curry_equiv A B C).symm_apply_apply e

def map_tensor {A A' B B' : AddCommGroup.{u}}
  (f : A ⟶ A') (g : B ⟶ B') : tensor A B ⟶ tensor A' B' :=
(tensor_product.map f.to_int_linear_map g.to_int_linear_map).to_add_monoid_hom

lemma id_helper (A : AddCommGroup.{u}) :
  (𝟙 A : A ⟶ A).to_int_linear_map = linear_map.id := rfl

lemma comp_helper {A B C : AddCommGroup.{u}}
  (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).to_int_linear_map = g.to_int_linear_map.comp f.to_int_linear_map := rfl

@[simp]
lemma zero_helper {A B : AddCommGroup.{u}} :
  (0 : A ⟶ B).to_int_linear_map = 0 := rfl

@[simp]
lemma map_tensor_id {A B : AddCommGroup.{u}} :
  map_tensor (𝟙 A) (𝟙 B) = 𝟙 _ :=
begin
  ext t, dsimp [map_tensor], simp [id_helper],
end

@[simp]
lemma map_tensor_comp_left {A A' A'' B : AddCommGroup.{u}} (f : A ⟶ A') (g : A' ⟶ A'') :
  map_tensor (f ≫ g) (𝟙 B) = map_tensor f (𝟙 _) ≫ map_tensor g (𝟙 _) :=
begin
  ext t,
  rw ← category.id_comp (𝟙 B),
  dsimp [map_tensor], simp only [comp_helper, id_helper, tensor_product.map_comp],
  simp,
end

@[simp]
lemma map_tensor_comp_right {A B B' B'' : AddCommGroup.{u}} (f : B ⟶ B') (g : B' ⟶ B'') :
  map_tensor (𝟙 A) (f ≫ g) = map_tensor (𝟙 _) f ≫ map_tensor (𝟙 _) g :=
begin
  ext t,
  rw ← category.id_comp (𝟙 A),
  dsimp [map_tensor], simp only [comp_helper, id_helper, tensor_product.map_comp],
  simp,
end

@[simp]
lemma map_tensor_comp_comp {A A' A'' B B' B'' : AddCommGroup.{u}}
  (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B') (g' : B' ⟶ B'') :
  map_tensor (f ≫ f') (g ≫ g') = map_tensor f g ≫ map_tensor f' g' :=
begin
  ext t,
  dsimp [map_tensor], simp only [comp_helper, id_helper, tensor_product.map_comp],
  simp,
end

lemma map_tensor_eq_comp {A A' B B' : AddCommGroup.{u}} (f : A ⟶ A') (g : B ⟶ B') :
  map_tensor f g = map_tensor f (𝟙 _) ≫ map_tensor (𝟙 _) g :=
begin
  nth_rewrite 0 ← category.id_comp g,
  nth_rewrite 0 ← category.comp_id f,
  rw map_tensor_comp_comp,
end

lemma map_tensor_eq_comp' {A A' B B' : AddCommGroup.{u}} (f : A ⟶ A') (g : B ⟶ B') :
  map_tensor f g = map_tensor (𝟙 _) g ≫ map_tensor f (𝟙 _) :=
begin
  nth_rewrite 0 ← category.id_comp f,
  nth_rewrite 0 ← category.comp_id g,
  rw map_tensor_comp_comp,
end

@[simp]
lemma map_tensor_zero_left {A A' B B' : AddCommGroup.{u}} (f : B ⟶ B') :
  map_tensor (0 : A ⟶ A') f = 0 :=
begin
  apply (tensor_curry_equiv _ _ _).injective,
  ext a b,
  dsimp [tensor_curry, map_tensor],
  simp,
end

@[simp]
lemma map_tensor_zero_right {A A' B B' : AddCommGroup.{u}} (f : A ⟶ A') :
  map_tensor f (0 : B ⟶ B') = 0 :=
begin
  apply (tensor_curry_equiv _ _ _).injective,
  ext a b,
  dsimp [tensor_curry, map_tensor],
  simp,
end

@[simp]
lemma map_tensor_add_right {A A' B B' : AddCommGroup.{u}} (f : A ⟶ A') (g₁ g₂ : B ⟶ B') :
  map_tensor f (g₁ + g₂) = map_tensor f g₁ + map_tensor f g₂ :=
begin
  apply (tensor_curry_equiv _ _ _).injective,
  ext a b,
  dsimp [tensor_curry, map_tensor],
  apply tensor_product.tmul_add,
end

@[simp]
lemma map_tensor_add_left {A A' B B' : AddCommGroup.{u}} (f₁ f₂ : A ⟶ A') (g : B ⟶ B') :
  map_tensor (f₁ + f₂) g = map_tensor f₁ g + map_tensor f₂ g :=
begin
  apply (tensor_curry_equiv _ _ _).injective,
  ext a b,
  dsimp [tensor_curry, map_tensor],
  apply tensor_product.add_tmul,
end

lemma tensor_uncurry_comp_curry {A B C D : AddCommGroup.{u}} (f : A ⟶ B) (g : B.tensor C ⟶ D) :
  tensor_uncurry (f ≫ tensor_curry g) = map_tensor f (𝟙 _) ≫ g :=
begin
  apply (tensor_curry_equiv _ _ _).injective,
  erw (tensor_curry_equiv _ _ _).apply_symm_apply,
  ext a c,
  dsimp [tensor_curry, tensor_curry_equiv, map_tensor],
  simp,
end

lemma tensor_curry_uncurry_comp {A B C D : AddCommGroup.{u}}
  (e : A ⟶ AddCommGroup.of (B ⟶ C)) (g : C ⟶ D):
  tensor_curry (tensor_uncurry e ≫ g) =
  e ≫ (preadditive_yoneda.flip.obj (opposite.op B)).map g :=
begin
  ext a b,
  dsimp [tensor_curry, tensor_uncurry, preadditive_yoneda],
  simp,
end

@[simps]
def tensor_functor : AddCommGroup.{u} ⥤ AddCommGroup.{u} ⥤ AddCommGroup.{u} :=
{ obj := λ A,
  { obj := λ B, tensor A B,
    map := λ B B' f, map_tensor (𝟙 _) f,
    map_id' := λ A, map_tensor_id,
    map_comp' := λ A B C f g, map_tensor_comp_right _ _ },
  map := λ A A' f,
  { app := λ B, map_tensor f (𝟙 _),
    naturality' := λ B C g, begin
      dsimp,
      rw [← map_tensor_eq_comp, ← map_tensor_eq_comp'],
    end },
  map_id' := begin
    intros A,
    ext B : 2,
    dsimp, exact map_tensor_id,
  end,
  map_comp' := begin
    intros A B C f g,
    ext B : 2,
    dsimp, exact map_tensor_comp_left _ _,
  end }
.

open opposite

def tensor_adj (B : AddCommGroup.{u}) :
  tensor_functor.flip.obj B ⊣ preadditive_coyoneda.obj (op B) :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ A C, (tensor_curry_equiv A B C).to_equiv,
  hom_equiv_naturality_left_symm' := λ A A' C f g, begin
    apply tensor_ext, intros x y,
    erw [tensor_curry_equiv_symm_apply, comp_apply, tensor_curry_equiv_symm_apply],
    dsimp only [tensor_uncurry],
    simp only [linear_map.comp_apply, tensor_product.lift.tmul, tensor_product.map_tmul,
      add_monoid_hom.coe_to_int_linear_map, id_apply, comp_apply], refl,
  end,
  hom_equiv_naturality_right' := λ A C C' f g, by { ext x y : 2, refl } }
.

instance tensor_flip_preserves_colimits (B : AddCommGroup.{u}) :
  limits.preserves_colimits (tensor_functor.flip.obj B) :=
(tensor_adj B).left_adjoint_preserves_colimits

def tensor_explicit_pi_comparison {α : Type u} [fintype α] (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) :
  tensor (AddCommGroup.of (direct_sum α (λ i, X i))) B ⟶
  AddCommGroup.of (direct_sum α (λ i, tensor (X i) B)) :=
direct_sum_lift.{u u+1} _ $ λ a, map_tensor (direct_sum_π.{u u+1} _ _) (𝟙 _)

def tensor_pi_comparison {α : Type u} (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) :
  tensor (∏ X) B ⟶ ∏ (λ a, tensor (X a) B) :=
limits.pi.lift $ λ b, map_tensor (limits.pi.π _ _) (𝟙 _)

open_locale classical

def tensor_explicit_pi_iso {α : Type u}
  (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) :
  (of (direct_sum α (λ (i : α), ↥(X i)))).tensor B ≅
  of (direct_sum α (λ (i : α), ↥((X i).tensor B))) :=
{ hom := tensor_uncurry $ direct_sum_desc.{u u+1} X $ λ i, tensor_curry $
    direct_sum_ι.{u u+1} _ i,
  inv := direct_sum_desc.{u u+1} _ $ λ i,
    map_tensor (direct_sum_ι.{u u+1} X i) (𝟙 _),
  hom_inv_id' := begin
    apply (tensor_curry_equiv _ _ _).injective,
    ext a b,
    dsimp [tensor_curry, tensor_uncurry, direct_sum_desc],
    simp only [comp_apply, linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul,
      linear_map.coe_comp, add_monoid_hom.coe_to_int_linear_map, add_monoid_hom.coe_mk,
      direct_sum.to_add_monoid_of, id_apply],
    dsimp [direct_sum_ι],
    simp only [direct_sum.to_add_monoid_of],
    dsimp [map_tensor],
    simp only [id_apply],
  end,
  inv_hom_id' := begin
    apply direct_sum_hom_ext'.{u u+1},
    intros i,
    simp only [direct_sum_ι_desc_assoc, category.comp_id],
    apply (tensor_curry_equiv _ _ _).injective,
    ext a b k,
    dsimp [tensor_curry, direct_sum_ι, direct_sum.of, map_tensor,
      tensor_uncurry, tensor_curry, direct_sum_desc],
    simp only [comp_apply, linear_map.to_add_monoid_hom_coe, tensor_product.map_tmul,
      add_monoid_hom.coe_to_int_linear_map, dfinsupp.single_add_hom_apply, id_apply,
      tensor_product.lift.tmul, linear_map.coe_comp, add_monoid_hom.coe_mk,
      dfinsupp.single_apply],
    dsimp [direct_sum.to_add_monoid],
    simp only [dfinsupp.sum_add_hom_single, add_monoid_hom.coe_mk, dfinsupp.single_apply]
  end }

lemma tensor_explicit_pi_iso_hom_eq {α : Type u} [fintype α]
  (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) :
  (tensor_explicit_pi_iso X B).hom = tensor_explicit_pi_comparison X B :=
begin
  symmetry,
  apply direct_sum_hom_ext.{u u+1}, swap, apply_instance,
  intros j,
  apply (tensor_curry_equiv _ _ _).injective,
  apply direct_sum_hom_ext'.{u u+1}, intros i,
  apply (tensor_curry_equiv _ _ _).symm.injective,
  dsimp,
  simp_rw tensor_uncurry_comp_curry,
  erw [direct_sum_lift_π, ← map_tensor_comp_comp, category.id_comp],
  dsimp only [tensor_explicit_pi_iso],
  erw [← category.assoc], let t := _, change _ = t ≫ _,
  have ht : t = direct_sum_ι.{u u+1} _ i,
  { dsimp [t],
    have := direct_sum_ι_desc.{u u+1} (λ i, tensor (X i) B)
      (λ i, map_tensor (direct_sum_ι.{u u+1} _ i) (𝟙 _)) i,
    dsimp at this, rw ← this, clear this,
    rw category.assoc,
    erw [(tensor_explicit_pi_iso X B).inv_hom_id, category.comp_id] },
  rw ht, clear ht, clear t,
  by_cases i = j,
  { subst h,
    simp [direct_sum_ι_π.{u u+1}] },
  { simp [direct_sum_ι_π_of_ne.{u u+1} _ _ _ h], }
end

instance is_iso_tensor_explicit_pi_comparison {α : Type u} [fintype α]
  (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) : is_iso (tensor_explicit_pi_comparison X B) :=
begin
  rw ← tensor_explicit_pi_iso_hom_eq,
  apply_instance
end

lemma tensor_explicit_pi_comparison_comparison {α : Type u}
  [fintype α]
  (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) :
  tensor_pi_comparison X B =
  map_tensor (direct_sum_lift.{u u+1} _ $ limits.pi.π _) (𝟙 _) ≫
  tensor_explicit_pi_comparison X B ≫
  limits.pi.lift (direct_sum_π.{u u+1} (λ i, tensor (X i) B)) :=
begin
  ext1,
  dsimp [tensor_pi_comparison],
  simp only [limits.limit.lift_π, limits.fan.mk_π_app, category.assoc],
  dsimp [tensor_explicit_pi_comparison],
  rw [direct_sum_lift_π, ← map_tensor_comp_left, direct_sum_lift_π],
end

instance is_iso_tensor_pi_comparison {α : Type u} [fintype α]
  (X : α → AddCommGroup.{u+1})
  (B : AddCommGroup.{u+1}) : is_iso (tensor_pi_comparison X B) :=
begin
  rw tensor_explicit_pi_comparison_comparison,
  apply_with is_iso.comp_is_iso { instances := ff },
  { change is_iso ((tensor_functor.flip.obj B).map _),
    apply_with functor.map_is_iso { instances := ff },
    change is_iso ((limits.limit.is_limit _).cone_point_unique_up_to_iso
      (is_limit_direct_sum_fan.{u u+1} X)).hom,
    apply_instance },
  apply_with is_iso.comp_is_iso { instances := ff }, apply_instance,
  change is_iso ((is_limit_direct_sum_fan.{u u+1} _).cone_point_unique_up_to_iso
    (limits.limit.is_limit _)).hom,
  apply_instance,
  apply_instance
end

def tensor_flip (A B : AddCommGroup.{u}) : A.tensor B ≅ B.tensor A :=
linear_equiv_to_iso (tensor_product.comm _ _ _)

def tensor_functor_iso_flip :
  tensor_functor.flip ≅ tensor_functor :=
nat_iso.of_components (λ A,
  nat_iso.of_components (λ B, tensor_flip _ _) begin
    intros U B f, apply tensor_ext, intros a b, refl,
  end) begin
    intros U V f, ext A : 2, apply tensor_ext, intros a b,
    refl,
  end

instance preserves_colimits_tensor_obj (A : AddCommGroup.{u}) :
  limits.preserves_colimits (tensor_functor.obj A) :=
limits.preserves_colimits_of_nat_iso (tensor_functor_iso_flip.app _)

section preserves_finite_limits

variables {X Y : AddCommGroup.{u}} (f : X ⟶ Y) [mono f]
  (A : AddCommGroup.{u})

def tensor_unit_iso_aux (t A : AddCommGroup.{u}) (ht : is_tensor_unit t) :
  t.tensor A ⟶ A :=
tensor_uncurry $ ht.as_hom (𝟙 _)

instance is_iso_tensor_unit_iso_aux (t A : AddCommGroup.{u}) (ht : is_tensor_unit t) :
  is_iso (tensor_unit_iso_aux t A ht) :=
begin
  let q : A ⟶ t.tensor A := ⟨λ a, ht.gen ⊗ₜ a, _ ,_⟩,
  use q, split,
  { apply_fun (tensor_curry_equiv _ _ _).to_equiv,
    dsimp [tensor_unit_iso_aux], rw tensor_curry_uncurry_comp, apply ht.ext,
    simp, dsimp [tensor_curry], simp },
  { ext, dsimp [q, tensor_unit_iso_aux, tensor_uncurry], simp, },
  { simp, },
  { intros x y, rw tensor_product.tmul_add },
end

def tensor_unit_iso (t A : AddCommGroup.{u}) (ht : is_tensor_unit t) :
  t.tensor A ≅ A :=
as_iso (tensor_unit_iso_aux t A ht)

lemma tensor_unit_iso_naturality (t A B : AddCommGroup.{u}) (ht : is_tensor_unit t) (f : A ⟶ B) :
  (tensor_unit_iso t A ht).hom ≫ f = map_tensor (𝟙 _) f ≫ (tensor_unit_iso t B ht).hom :=
begin
  apply_fun (tensor_curry_equiv _ _ _).to_equiv,
  dsimp [tensor_unit_iso, tensor_unit_iso_aux],
  rw tensor_curry_uncurry_comp,
  apply ht.ext,
  simp, dsimp, simp,
  ext, dsimp [tensor_curry, map_tensor, tensor_uncurry],
  simp,
end

instance tensor_obj_map_preserves_mono [no_zero_smul_divisors ℤ A] :
  mono ((tensor_functor.obj A).map f) :=
begin
  let D := A.diagram,
  let T := A.cocone,
  let hT : limits.is_colimit T := A.is_colimit_cocone,
  let FX : A.index_cat ⥤ AddCommGroup :=
    D ⋙ tensor_functor.flip.obj X,
  let FY : A.index_cat ⥤ AddCommGroup :=
    D ⋙ tensor_functor.flip.obj Y,
  let η : FX ⟶ FY := whisker_left _ (tensor_functor.flip.map f),
  let eX : tensor A X ≅ limits.colimit FX :=
    (limits.is_colimit_of_preserves
    (tensor_functor.flip.obj X) hT).cocone_point_unique_up_to_iso
    (limits.colimit.is_colimit _),
  let eY : tensor A Y ≅ limits.colimit FY :=
    (limits.is_colimit_of_preserves
    (tensor_functor.flip.obj Y) hT).cocone_point_unique_up_to_iso
    (limits.colimit.is_colimit _),
  let t := _, change mono t,
  have ht : t = eX.hom ≫ limits.colim_map η ≫ eY.inv,
  { dsimp [t, eX, eY],
    apply (limits.is_colimit_of_preserves (tensor_functor.flip.obj X) hT).hom_ext,
    intros i,
    erw (limits.is_colimit_of_preserves (tensor_functor.flip.obj X) hT).fac_assoc,
    simp only [functor.map_cocone_ι_app, functor.flip_obj_map,
      tensor_functor_map_app, limits.colimit.cocone_ι,
      limits.ι_colim_map_assoc, whisker_left_app, functor.flip_map_app,
      tensor_functor_obj_map, limits.colimit.comp_cocone_point_unique_up_to_iso_inv],
    simp only [← map_tensor_comp_comp, category.id_comp, category.comp_id],
    dsimp, erw category.comp_id },
  rw ht, clear ht t,
  suffices : mono (limits.colim_map η),
  { resetI, apply_instance },
  suffices : ∀ i, mono (η.app i),
  { resetI, apply mono_colim_map_of_mono },
  intros i,
  obtain ⟨α, _, e, -⟩ := exists_sigma_iso_of_index _ i, resetI,
  change mono ((tensor_functor.obj (of i.val)).map f),
  clear eX eY,
  let eX : ((tensor_functor.obj (of i.val)).obj X) ≅
    (tensor_functor.obj (∐ λ (i : α), tunit)).obj X := (tensor_functor.map_iso e.symm).app X,
  let eY : ((tensor_functor.obj (of i.val)).obj Y) ≅
    (tensor_functor.obj (∐ λ (i : α), tunit)).obj Y := (tensor_functor.map_iso e.symm).app Y,
  have : (tensor_functor.obj (of ↥(i.val))).map f =
    eX.hom ≫ (tensor_functor.obj _).map f ≫ eY.inv,
  { dsimp [eX, eY],
    simpa only [← map_tensor_comp_comp, category.id_comp, category.comp_id, e.inv_hom_id] },
  rw this, clear this,
  suffices : mono ((tensor_functor.obj (∐ λ (i : α), tunit)).map f), { resetI, apply_instance },
  clear eX eY e i η FX FY D,
  let eX : (tensor_functor.obj (∐ λ (i : α), tunit)).obj X ≅
    (∐ (λ i : α, tensor tunit X)) :=
    preserves_colimit_iso (tensor_functor.flip.obj X) _ ≪≫
    limits.has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ _, iso.refl _),
  let eY : (tensor_functor.obj (∐ λ (i : α), tunit)).obj Y ≅
    (∐ (λ i : α, tensor tunit Y)) :=
    preserves_colimit_iso (tensor_functor.flip.obj Y) _ ≪≫
    limits.has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ _, iso.refl _),
  have : (tensor_functor.obj (∐ λ (i : α), tunit)).map f =
    eX.hom ≫ _ ≫ eY.inv,
  rotate 2,
  { apply limits.sigma.desc,
    intros i, refine _ ≫ limits.sigma.ι _ i,
    exact map_tensor (𝟙 _) f },
  { dsimp [eX, eY],
    apply (limits.is_colimit_of_preserves (tensor_functor.flip.obj X) _).hom_ext,
    rotate,
    { apply limits.colimit.is_colimit },
    { apply_instance },
    rintro ⟨j⟩,
    slice_rhs 1 2
    { erw (limits.is_colimit_of_preserves (tensor_functor.flip.obj X)
      (limits.colimit.is_colimit _)).fac },
    dsimp,
    simp only [limits.has_colimit.iso_of_nat_iso_ι_hom, discrete.nat_iso_hom_app,
      category.assoc, limits.colimit.ι_desc, limits.cofan.mk_ι_app,
      limits.has_colimit.iso_of_nat_iso_ι_inv, discrete.nat_iso_inv_app,
      ι_preserves_colimits_iso_inv, functor.flip_obj_map, tensor_functor_map_app],
    dsimp, simp only [category.id_comp, ← map_tensor_comp_comp, category.comp_id], },
  rw this, clear this,
  let t := _, change mono (eX.hom ≫ t ≫ eY.inv),
  suffices : mono t, { resetI, apply_instance },
  suffices : mono (map_tensor (𝟙 tunit) f),
  { apply AB4.cond, intros i, assumption },
  clear eX eY,
  let eX : tunit.tensor X ≅ X := tensor_unit_iso _ _ is_tensor_unit_tunit,
  let eY : tunit.tensor Y ≅ Y := tensor_unit_iso _ _ is_tensor_unit_tunit,
  have : map_tensor (𝟙 tunit) f = eX.hom ≫ f ≫ eY.inv,
  { simp [reassoc_of (tensor_unit_iso_naturality tunit X Y is_tensor_unit_tunit f)] },
  rw this, apply_instance,
end

end preserves_finite_limits

instance tensor_functor_additive (A : AddCommGroup.{u}) :
  (tensor_functor.obj A).additive := { }

instance tensor_functor_flip_additive (A : AddCommGroup.{u}) :
  (tensor_functor.flip.obj A).additive := { }

end AddCommGroup
