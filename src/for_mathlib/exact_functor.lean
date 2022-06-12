import category_theory.abelian.homology
import for_mathlib.abelian_category

namespace category_theory

universes v u u'
variables {A : Type u} {B : Type u'} [category.{v} A] [category.{v} B]
  [abelian A] [abelian B] (F : A ⥤ B) [functor.additive F]

lemma exact.mono_desc {X Y Z : A} {f : X ⟶ Y} {g : Y ⟶ Z} (e : exact f g) :
  mono (limits.cokernel.desc _ _ e.w) :=
abelian.category_theory.limits.cokernel.desc.category_theory.mono f g e --WAT?

lemma exact.epi_lift {X Y Z : A} {f : X ⟶ Y} {g : Y ⟶ Z} (e : exact f g) :
  epi (limits.kernel.lift _ _ e.w) :=
limits.kernel.lift.epi e

lemma exact.epi_of_exact_zero_right {X Y Z : A} {f : X ⟶ Y} (e : exact f (0 : Y ⟶ Z)) :
  epi f :=
begin
  rw abelian.epi_iff_cokernel_π_eq_zero,
  rw abelian.exact_iff at e,
  cases e with e1 e2,
  simpa using e2,
end

lemma exact.mono_of_exact_zero_left {X Y Z : A} {f : Y ⟶ Z} (e : exact (0 : X ⟶ Y) f) :
  mono f :=
begin
  rw abelian.mono_iff_kernel_ι_eq_zero,
  rw abelian.exact_iff at e,
  cases e with e1 e2,
  simpa using e2,
end

namespace functor

open category_theory.limits

class exact : Prop :=
(cond [] : ∀ {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z), exact f g → exact (F.map f) (F.map g))

variables [exact F]

noncomputable theory

-- Sanity check
example : preserves_zero_morphisms F := infer_instance

open_locale zero_object classical

instance epi_of_epi_of_exact {X Y : A} (f : X ⟶ Y)
  [epi f] : epi (F.map f) :=
begin
  have : category_theory.exact f (0 : _ ⟶ 0) := exact_epi_zero f,
  replace this := exact.cond F _ _ this,
  simp at this,
  apply this.epi_of_exact_zero_right,
end

instance mono_of_mono_of_exact {X Y : A} (f : X ⟶ Y)
  [mono f] : mono (F.map f) :=
begin
  have : category_theory.exact (0 : X ⟶ _) f := exact_zero_left_of_mono X,
  replace this := exact.cond F _ _ this,
  simp at this,
  apply this.mono_of_exact_zero_left,
end

instance {X Y : A} (f : X ⟶ Y) : is_iso (cokernel_comparison f F) :=
begin
  have : category_theory.exact (F.map f) (F.map (cokernel.π f)),
  { apply exact.cond, exact abelian.exact_cokernel f },
  dsimp [cokernel_comparison],
  apply_with is_iso_of_mono_of_epi { instances := ff },
  apply_instance,
  apply this.mono_desc,
  constructor, intros Z a b h,
  apply_fun (λ e, cokernel.π _ ≫ e) at h,
  simp at h,
  rwa cancel_epi at h,
end

instance preserves_finite_colimits : preserves_finite_colimits F :=
begin
  apply_with preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts { instances := ff },
  any_goals { apply_instance },
  { sorry }, -- use cokernel iso above
  { introsI J hI,
    apply preserves_coproducts_of_shape_of_preserves_biproducts_of_shape }
end

instance {X Y : A} (f : X ⟶ Y) : is_iso (kernel_comparison f F) :=
begin
  have : category_theory.exact (F.map (kernel.ι f)) (F.map f),
  { apply exact.cond, exact exact_kernel_ι },
  dsimp [kernel_comparison],
  apply_with is_iso_of_mono_of_epi { instances := ff },
  apply_instance,
  constructor,
  intros Z a b h,
  apply_fun (λ e, e ≫ kernel.ι _) at h,
  simp at h,
  rwa cancel_mono at h,
  apply this.epi_lift,
end

instance preserves_finite_limits : preserves_finite_limits F :=
begin
  apply_with preserves_finite_limits_of_preserves_equalizers_and_finite_products { instances := ff },
  any_goals { apply_instance },
  { sorry }, -- use kernel iso above
  { introsI J hJ,
    apply preserves_products_of_shape_of_preserves_biproducts_of_shape }
end

def homology_iso {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w w') :
  F.obj (homology f g w) ≅ homology (F.map f) (F.map g) w' :=
{ hom := homology.lift _ _ _ (F.map (homology.ι _ _ _) ≫
    category_theory.inv (cokernel_comparison _ _)) sorry,
  inv := homology.desc' _ _ _ (category_theory.inv (kernel_comparison _ _) ≫
    F.map (homology.π' _ _ _)) sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

end functor

-- TODO: Exact iff preserves finite limits and colimits

end category_theory
