import category_theory.abelian.homology
import algebra.homology.additive
import for_mathlib.abelian_category
import for_mathlib.equalizers

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

def exact : Prop :=
∀ ⦃X Y Z : A⦄ (f : X ⟶ Y) (g : Y ⟶ Z), exact f g → exact (F.map f) (F.map g)

noncomputable theory

-- Sanity check
example : preserves_zero_morphisms F := infer_instance

open_locale zero_object classical

lemma epi_of_epi_of_exact (h : F.exact) {X Y : A} (f : X ⟶ Y)
  [epi f] : epi (F.map f) :=
begin
  have : category_theory.exact f (0 : _ ⟶ 0) := exact_epi_zero f,
  replace this := h _ _ this,
  simp at this,
  apply this.epi_of_exact_zero_right,
end

lemma mono_of_mono_of_exact (h : F.exact) {X Y : A} (f : X ⟶ Y)
  [mono f] : mono (F.map f) :=
begin
  have : category_theory.exact (0 : X ⟶ _) f := exact_zero_left_of_mono X,
  replace this := h _ _ this,
  simp at this,
  apply this.mono_of_exact_zero_left,
end

lemma is_iso_cokernel_comparison_of_exact
  (hh : F.exact) {X Y : A} (f : X ⟶ Y) : is_iso (cokernel_comparison f F) :=
begin
  have : category_theory.exact (F.map f) (F.map (cokernel.π f)),
  { apply hh, exact abelian.exact_cokernel f },
  dsimp [cokernel_comparison],
  apply_with is_iso_of_mono_of_epi { instances := ff },
  apply_instance,
  apply this.mono_desc,
  constructor, intros Z a b h,
  apply_fun (λ e, cokernel.π _ ≫ e) at h,
  simp at h,
  haveI := epi_of_epi_of_exact _ hh (cokernel.π f),
  rwa cancel_epi at h,
end

lemma preserves_coequalizers_of_exact (hh : F.exact) {X Y : A} (f g : X ⟶ Y) :
  preserves_colimit (parallel_pair f g) F :=
preserves_colimit_of_preserves_colimit_cocone (cofork_of_cokernel_is_colimit _ _)
begin
  let e : parallel_pair f g ⋙ F ≅ parallel_pair (F.map f) (F.map g) :=
    diagram_iso_parallel_pair _,
  equiv_rw (is_colimit.precompose_inv_equiv e _).symm,
  apply is_colimit.of_iso_colimit (cofork_of_cokernel_is_colimit (F.map f) (F.map g)),
  haveI := is_iso_cokernel_comparison_of_exact F hh (f-g),
  refine cocones.ext (cokernel.map_iso (F.map f - F.map g) (F.map (f-g))
    (iso.refl _) (iso.refl _) (by simp) ≪≫ as_iso (cokernel_comparison (f-g) F)) _,
  rintro (_|_),
  tidy,
end

lemma preserves_finite_colimits_of_exact (hh : F.exact) : preserves_finite_colimits F :=
begin
  apply_with preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts
    { instances := ff },
  any_goals { apply_instance },
  { constructor,
    intro K,
    apply_with preserves_colimit_of_iso_diagram { instances := ff },
    exact (diagram_iso_parallel_pair K).symm,
    apply preserves_coequalizers_of_exact F hh, },
  { introsI J hI,
    apply preserves_coproducts_of_shape_of_preserves_biproducts_of_shape }
end

lemma is_iso_kernel_comparison_of_exact
  (hh : F.exact) {X Y : A} (f : X ⟶ Y) : is_iso (kernel_comparison f F) :=
begin
  have : category_theory.exact (F.map (kernel.ι f)) (F.map f),
  { apply hh, exact exact_kernel_ι },
  dsimp [kernel_comparison],
  apply_with is_iso_of_mono_of_epi { instances := ff },
  apply_instance,
  constructor,
  intros Z a b h,
  apply_fun (λ e, e ≫ kernel.ι _) at h,
  simp at h,
  haveI := mono_of_mono_of_exact _ hh (kernel.ι f),
  rwa cancel_mono at h,
  apply this.epi_lift,
end

lemma preserves_equalizers_of_exact (hh : F.exact) {X Y : A} (f g : X ⟶ Y) :
  preserves_limit (parallel_pair f g) F :=
preserves_limit_of_preserves_limit_cone (fork_of_kernel_is_limit _ _)
begin
  let e : parallel_pair f g ⋙ F ≅ parallel_pair (F.map f) (F.map g) :=
    diagram_iso_parallel_pair _,
  equiv_rw (is_limit.postcompose_hom_equiv e _).symm,
  apply is_limit.of_iso_limit (fork_of_kernel_is_limit (F.map f) (F.map g)),
  haveI := is_iso_kernel_comparison_of_exact F hh (f-g),
  symmetry,
  refine cones.ext (as_iso (kernel_comparison (f-g) F) ≪≫
    kernel.map_iso (F.map (f-g)) (F.map f - F.map g) (iso.refl _) (iso.refl _) (by simp)) _,
  rintro (_|_),
  tidy,
end

lemma preserves_finite_limits_of_exact (h : F.exact) : preserves_finite_limits F :=
begin
  apply_with preserves_finite_limits_of_preserves_equalizers_and_finite_products
    { instances := ff },
  any_goals { apply_instance },
  { constructor,
    intro K,
    apply_with preserves_limit_of_iso_diagram { instances := ff },
    exact (diagram_iso_parallel_pair K).symm,
    apply preserves_equalizers_of_exact F h, },
  { introsI J hJ,
    apply preserves_products_of_shape_of_preserves_biproducts_of_shape }
end

variables [preserves_finite_limits F] [preserves_finite_colimits F]

def homology_iso {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w w') :
  F.obj (homology f g w) ≅ homology (F.map f) (F.map g) w' :=
{ hom := homology.lift _ _ _ (F.map (homology.ι _ _ _) ≫
    category_theory.inv (cokernel_comparison _ _)) sorry,
  inv := homology.desc' _ _ _ (category_theory.inv (kernel_comparison _ _) ≫
    F.map (homology.π' _ _ _)) sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

def homology_functor_iso {M : Type*} (c : complex_shape M) (i : M) :
  homology_functor A c i ⋙ F ≅
  F.map_homological_complex _ ⋙ homology_functor B c i :=
nat_iso.of_components
(λ X,
{ hom := homology.lift _ _ _
   (F.map (homology.ι _ _ _) ≫ category_theory.inv (cokernel_comparison _ _) ≫
    cokernel.desc _ (cokernel.π _) sorry) sorry,
  inv := homology.desc' _ _ _
    (kernel.lift _ (kernel.ι _) sorry ≫
    category_theory.inv (kernel_comparison _ _) ≫ F.map (homology.π' _ _ _))
    sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry })
sorry

end functor

-- TODO: Exact iff preserves finite limits and colimits

end category_theory
