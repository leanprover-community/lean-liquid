import category_theory.abelian.homology
import algebra.homology.additive
import for_mathlib.abelian_category
import for_mathlib.equalizers
import for_mathlib.homology_map_datum
import for_mathlib.short_complex
import for_mathlib.derived.defs

namespace category_theory

universes v u u'
variables {A : Type u} {B : Type u'} [category.{v} A] [category.{v} B]
  [abelian A] [abelian B] (F G : A ⥤ B) [functor.additive F] [functor.additive G] (φ : F ⟶ G)

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

def preserves_coequalizers_of_exact (hh : F.exact) {X Y : A} (f g : X ⟶ Y) :
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

def preserves_finite_colimits_of_exact (hh : F.exact) : preserves_finite_colimits F :=
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

def preserves_equalizers_of_exact (hh : F.exact) {X Y : A} (f g : X ⟶ Y) :
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

def preserves_finite_limits_of_exact (h : F.exact) : preserves_finite_limits F :=
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
variables [preserves_finite_limits G] [preserves_finite_colimits G]

def homology_nat_iso :
  (short_complex.homology_functor : short_complex A ⥤ A) ⋙ F ≅
    F.map_short_complex ⋙ short_complex.homology_functor :=
nat_iso.of_components
  (λ S, ((homology_iso_datum.tautological' S.1.f S.1.g S.2).apply_exact_functor F).iso)
  (λ S₁ S₂ φ, by simp only [comp_map, iso.hom_inv_id_assoc,
    ((homology_map_datum.tautological' φ).map_exact_functor F).homology_map_eq])

def homology_iso {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w w') :
  F.obj (homology f g w) ≅ homology (F.map f) (F.map g) w' :=
F.homology_nat_iso.app (short_complex.mk f g w)

def homology_functor_iso {M : Type*} (c : complex_shape M) (i : M) :
  homology_functor A c i ⋙ F ≅
  F.map_homological_complex _ ⋙ homology_functor B c i :=
begin
  calc homology_functor A c i ⋙ F ≅
    (short_complex.functor_homological_complex A c i ⋙ short_complex.homology_functor) ⋙ F : _
  ... ≅ short_complex.functor_homological_complex A c i ⋙ short_complex.homology_functor ⋙ F : _
  ... ≅ short_complex.functor_homological_complex A c i ⋙ F.map_short_complex ⋙
    short_complex.homology_functor : _
  ... ≅ (short_complex.functor_homological_complex A c i ⋙ F.map_short_complex) ⋙
    short_complex.homology_functor : _
  ... ≅ (F.map_homological_complex _ ⋙ short_complex.functor_homological_complex B c i) ⋙
    short_complex.homology_functor : _
  ... ≅ F.map_homological_complex _ ⋙ (short_complex.functor_homological_complex B c i) ⋙
    short_complex.homology_functor : _
  ... ≅ F.map_homological_complex _ ⋙ homology_functor B c i : _,
  { exact iso_whisker_right (short_complex.homology_functor_iso A c i) F, },
  { apply associator, },
  { exact iso_whisker_left _ (F.homology_nat_iso), },
  { symmetry, apply associator, },
  { exact iso_whisker_right (short_complex.functor_homological_complex_map F c i) _, },
  { apply associator, },
  { exact iso_whisker_left _ (short_complex.homology_functor_iso B c i).symm, },
end

variables {F G}

def naturality_homology_nat_iso_app (S : short_complex A) :
  φ.app (S.homology) ≫ G.homology_nat_iso.hom.app S =
    F.homology_nat_iso.hom.app S ≫
      short_complex.homology_functor.map (φ.map_short_complex.app S) :=
begin
  let h := (homology_iso_datum.tautological' S.val.f S.val.g S.zero),
  simpa [← cancel_epi (h.apply_exact_functor F).iso.hom, iso.hom_inv_id_assoc]
    using (h.map_nat_trans φ).homology_map_eq.symm,
end

/-- naturality of `homology_functor_iso` on the variable `F` -/
lemma naturality_homology_functor_iso_hom_app {M : Type*} {c : complex_shape M}
  (X : homological_complex A c) (i : M) :
  φ.app ((homology_functor A c i).obj X) ≫ (G.homology_functor_iso c i).hom.app X =
  (F.homology_functor_iso c i).hom.app X ≫
    (homology_functor B c i).map ((nat_trans.map_homological_complex φ c).app X) :=
begin
  dsimp only [homology_functor_iso, iso.trans, iso_whisker_left, whiskering_left,
    whisker_left, iso_whisker_right, whiskering_right, whisker_right, map_iso,
    associator, iso.symm, short_complex.homology_functor_iso,
    nat_iso.of_components, iso.refl],
  simp only [category.assoc, nat_trans.comp_app, category.id_comp, F.map_id, G.map_id],
  erw [category.id_comp, category.id_comp, category.comp_id],
  slice_lhs 1 2 { erw naturality_homology_nat_iso_app φ
    ((short_complex.functor_homological_complex A c i).obj X), },
  rw [category.assoc, ← short_complex.homology_functor.map_comp],
    simpa only [short_complex.naturality_functor_homological_complex_map,
      short_complex.homology_functor.map_comp],
end

lemma naturality_homology_functor_iso {M : Type*} (c : complex_shape M) (i : M) :
  𝟙 (homology_functor A c i) ◫ φ ≫ (G.homology_functor_iso c i).hom =
  (F.homology_functor_iso c i).hom ≫
    nat_trans.map_homological_complex φ c ◫ (𝟙 (homology_functor B c i)) :=
begin
  ext1, ext1 X,
  simp only [nat_trans.comp_app, nat_trans.hcomp_app, nat_trans.id_app, G.map_id,
    category.comp_id],
  erw category.id_comp,
  apply naturality_homology_functor_iso_hom_app,
end

variable (F)

def homology_functor_iso_on_homotopy_category {M : Type*} (c : complex_shape M) (i : M) :
  homotopy_category.homology_functor A c i ⋙ F ≅
  F.map_homotopy_category _ ⋙ homotopy_category.homology_functor B c i :=
nat_iso.of_components
(λ X, (F.homology_functor_iso c i).app X.as)
(λ X Y f, begin
  nth_rewrite 0 ← homotopy_category.quotient_map_out f,
  erw (F.homology_functor_iso c i).hom.naturality (quot.out f),
  refl,
end)

def map_quasi_iso_on_homotopy_category {M : Type*} {c : complex_shape M}
  {X₁ X₂ : homotopy_category A c} (φ : X₁ ⟶ X₂) [hφ : homotopy_category.is_quasi_iso φ] :
  homotopy_category.is_quasi_iso ((F.map_homotopy_category c).map φ) :=
⟨begin
  intro i,
  let F₁ := homotopy_category.homology_functor A c i ⋙ F,
  let F₂ := map_homotopy_category c F ⋙ homotopy_category.homology_functor B c i,
  change is_iso (F₂.map φ),
  let e : F₁ ≅ F₂ := F.homology_functor_iso_on_homotopy_category c i,
  have h := e.hom.naturality φ,
  rw [← cancel_epi (e.inv.app X₁)] at h,
  conv_rhs at h { rw [← category.assoc, ← nat_trans.comp_app, e.inv_hom_id], },
  rw [nat_trans.id_app, category.id_comp] at h,
  rw ← h,
  haveI : is_iso (F₁.map φ) := begin
    haveI := hφ.cond,
    dsimp only [F₁, functor.comp],
    apply functor.map_is_iso,
  end,
  apply_instance,
end⟩

end functor

-- TODO: Exact iff preserves finite limits and colimits
end category_theory
