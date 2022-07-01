import for_mathlib.short_complex_projections
import for_mathlib.homological_complex_abelian
import for_mathlib.homology_map_datum
import for_mathlib.abelian_sheaves.functor_category
import for_mathlib.short_complex_functor_category

noncomputable theory

open category_theory category_theory.category category_theory.limits
open_locale zero_object

universes v

namespace short_complex

section construction

variables {C : Type*} [category C] [has_zero_morphisms C]
variables {J : Type*} [category J] (F : J ⥤ short_complex C)
  [has_colimit (F ⋙ π₁)] [has_colimit (F ⋙ π₂)] [has_colimit (F ⋙ π₃)]

@[simps]
def colimit_cocone.cocone : cocone F :=
{ X := mk (colim_map (𝟙 F ◫ φ₁₂)) (colim_map (𝟙 F ◫ φ₂₃)) begin
    ext,
    dsimp,
    simp only [ι_colim_map_assoc, nat_trans.hcomp_app, φ₁₂_app, nat_trans.id_app, π₂_map,
      ι_colim_map, φ₂₃_app, π₃_map, assoc, comp_zero],
    erw [composable_morphisms.id_τ₂, id_comp, (F.obj j).zero_assoc, zero_comp],
  end,
  ι :=
    { app := λ j, begin
        refine ⟨colimit.ι (F ⋙ π₁) j, colimit.ι (F ⋙ π₂) j, colimit.ι (F ⋙ π₃) j, _, _⟩,
        { dsimp,
          simp only [ι_colim_map, nat_trans.hcomp_app, φ₁₂_app, nat_trans.id_app, π₂_map,
            assoc],
          erw [composable_morphisms.id_τ₂, id_comp],
          refl, },
        { dsimp,
          simp only [ι_colim_map, nat_trans.hcomp_app, φ₂₃_app, nat_trans.id_app, π₃_map,
            assoc],
          erw [composable_morphisms.id_τ₃, id_comp],
          refl, },
      end,
      naturality' := λ i j f, begin
        ext,
        { dsimp, simpa only [comp_id] using colimit.w (F ⋙ π₁) f, },
        { dsimp, simpa only [comp_id] using colimit.w (F ⋙ π₂) f, },
        { dsimp, simpa only [comp_id] using colimit.w (F ⋙ π₃) f, },
      end }, }

def colimit_cocone : colimit_cocone F :=
{ cocone := colimit_cocone.cocone F,
  is_colimit :=
  { desc := λ s, begin
      refine ⟨colimit.desc (F ⋙ π₁) (π₁.map_cocone s),
        colimit.desc (F ⋙ π₂) (π₂.map_cocone s),
        colimit.desc (F ⋙ π₃) (π₃.map_cocone s), _, _⟩,
      { ext,
        dsimp,
        simp only [ι_colim_map_assoc, nat_trans.hcomp_app, φ₁₂_app, nat_trans.id_app,
          π₂_map, colimit.ι_desc, functor.map_cocone_ι_app, assoc, colimit.ι_desc_assoc, π₁_map],
        erw [composable_morphisms.id_τ₂, id_comp],
        exact (s.ι.app j).comm₁₂, },
      { ext,
        dsimp,
        simp only [ι_colim_map_assoc, nat_trans.hcomp_app, φ₂₃_app, nat_trans.id_app,
          π₃_map, colimit.ι_desc, functor.map_cocone_ι_app, assoc, colimit.ι_desc_assoc, π₂_map],
        erw [composable_morphisms.id_τ₃, id_comp],
        exact (s.ι.app j).comm₂₃, },
    end,
    fac' := λ s j, begin
      ext,
      { dsimp, simp only [colimit.ι_desc, functor.map_cocone_ι_app, π₁_map], },
      { dsimp, simp only [colimit.ι_desc, functor.map_cocone_ι_app, π₂_map], },
      { dsimp, simp only [colimit.ι_desc, functor.map_cocone_ι_app, π₃_map], },
    end,
    uniq' := λ s m hm, begin
      have h₁ := λ j, congr_arg (λ (φ : F.obj j ⟶ s.X), π₁.map φ) (hm j),
      have h₂ := λ j, congr_arg (λ (φ : F.obj j ⟶ s.X), π₂.map φ) (hm j),
      have h₃ := λ j, congr_arg (λ (φ : F.obj j ⟶ s.X), π₃.map φ) (hm j),
      dsimp at h₁ h₂ h₃,
      ext,
      { dsimp, simp only [h₁, colimit.ι_desc, functor.map_cocone_ι_app, π₁_map], },
      { dsimp, simp only [h₂, colimit.ι_desc, functor.map_cocone_ι_app, π₂_map], },
      { dsimp, simp only [h₃, colimit.ι_desc, functor.map_cocone_ι_app, π₃_map], },
    end, }, }

instance : has_colimit F := ⟨nonempty.intro (colimit_cocone F)⟩

def π₁_preserves_colimit : preserves_colimit F (π₁ : short_complex C ⥤ C) :=
preserves_colimit_of_preserves_colimit_cocone (colimit_cocone F).is_colimit
  (is_colimit.of_iso_colimit (get_colimit_cocone (F ⋙ π₁)).is_colimit
    (cocones.ext (iso.refl _) (λ j, comp_id _)))

def π₂_preserves_colimit : preserves_colimit F (π₂ : short_complex C ⥤ C) :=
preserves_colimit_of_preserves_colimit_cocone (colimit_cocone F).is_colimit
  (is_colimit.of_iso_colimit (get_colimit_cocone (F ⋙ π₂)).is_colimit
    (cocones.ext (iso.refl _) (λ j, comp_id _)))

def π₃_preserves_colimit : preserves_colimit F (π₃ : short_complex C ⥤ C) :=
preserves_colimit_of_preserves_colimit_cocone (colimit_cocone F).is_colimit
  (is_colimit.of_iso_colimit (get_colimit_cocone (F ⋙ π₃)).is_colimit
    (cocones.ext (iso.refl _) (λ j, comp_id _)))

end construction

section preserves

variables {C : Type*} [category C] [has_zero_morphisms C]
variables {J D : Type*} [category J] [category D]

def π₁₂₃_reflects_colimits {F : J ⥤ short_complex C} (s : cocone F)
  (h₁ : is_colimit (π₁.map_cocone s)) (h₂ : is_colimit (π₂.map_cocone s))
  (h₃ : is_colimit (π₃.map_cocone s)) :
  is_colimit s :=
begin
  haveI : has_colimit (F ⋙ π₁) := ⟨nonempty.intro ⟨_, h₁⟩⟩,
  haveI : has_colimit (F ⋙ π₂) := ⟨nonempty.intro ⟨_, h₂⟩⟩,
  haveI : has_colimit (F ⋙ π₃) := ⟨nonempty.intro ⟨_, h₃⟩⟩,
  refine is_colimit.of_iso_colimit (colimit_cocone F).is_colimit (cocones.ext _ _),
  { suffices : is_iso ((colimit_cocone F).is_colimit.desc s),
    { haveI := this,
      exact as_iso ((colimit_cocone F).is_colimit.desc s), },
    apply is_iso_of_is_isos,
    { exact is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) h₁), },
    { exact is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) h₂), },
    { exact is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso
        (colimit.is_colimit _) h₃), }, },
  { intro j,
    simp only [as_iso_hom, is_colimit.fac], },
end

def π₁₂₃_reflect_preserves_colimits (G : J ⥤ D) (F : D ⥤ short_complex C)
  (h₁ : preserves_colimit G (F ⋙ π₁)) (h₂ : preserves_colimit G (F ⋙ π₂))
  (h₃ : preserves_colimit G (F ⋙ π₃)) : preserves_colimit G F :=
⟨λ s hs, π₁₂₃_reflects_colimits _
  (@is_colimit_of_preserves _ _ _ _ _ _ G (F ⋙ π₁) _ hs _)
  (@is_colimit_of_preserves _ _ _ _ _ _ G (F ⋙ π₂) _ hs _)
  (@is_colimit_of_preserves _ _ _ _ _ _ G (F ⋙ π₃) _ hs _)⟩

variable (J)

def preserves_colimits_of_shape_of_projections (F : D ⥤ short_complex C)
  (h₁ : preserves_colimits_of_shape J (F ⋙ π₁))
  (h₂ : preserves_colimits_of_shape J (F ⋙ π₂))
  (h₃ : preserves_colimits_of_shape J (F ⋙ π₃)) :
  preserves_colimits_of_shape J F :=
⟨by { intro G, apply π₁₂₃_reflect_preserves_colimits; apply_instance, }⟩

end preserves

section functor_homological_complex

variables {C : Type*} [category C] [abelian C]
variables {M : Type*} {c : complex_shape M}
variables {J : Type*} [category J]

instance zero_preserves_colimits_of_shape {D : Type*} [category D]:
  preserves_colimits_of_shape J (0 : D ⥤ C) :=
⟨λ F, ⟨λ s hs,
{ desc := λ t, 0,
  fac' := λ t j, begin
    dsimp,
    apply is_zero.eq_of_src,
    apply is_zero.obj,
    apply is_zero_zero,
  end,
  uniq' := λ t m j, begin
    dsimp,
    apply is_zero.eq_of_src,
    apply is_zero.obj,
    apply is_zero_zero,
  end, }⟩⟩

lemma functor_homological_complex_π₁_iso_zero (i : M) (h : c.prev i = none) :
  functor_homological_complex C c i ⋙ π₁ ≅ 0 :=
begin
  refine is_zero.iso _ (is_zero_zero _),
  rw is_zero.iff_id_eq_zero,
  ext X,
  apply is_zero.eq_of_src,
  exact is_zero.of_iso (is_zero_zero _) (X.X_prev_iso_zero h),
end

lemma functor_homological_complex_π₃_iso_zero (i : M) (h : c.next i = none) :
  functor_homological_complex C c i ⋙ π₃ ≅ 0 :=
begin
  refine is_zero.iso _ (is_zero_zero _),
  rw is_zero.iff_id_eq_zero,
  ext X,
  apply is_zero.eq_of_src,
  exact is_zero.of_iso (is_zero_zero _) (X.X_next_iso_zero h),
end

lemma functor_homological_complex_π₁_iso_eval (i j : M) (hij : c.rel j i) :
  functor_homological_complex C c i ⋙ π₁ ≅ homological_complex.eval C c j :=
nat_iso.of_components (λ X, X.X_prev_iso hij)
(λ X Y f, begin
  dsimp,
  simp only [homological_complex.hom.prev_eq f hij, assoc, iso.inv_hom_id, comp_id],
end)

lemma functor_homological_complex_π₃_iso_eval (i j : M) (hij : c.rel i j) :
  functor_homological_complex C c i ⋙ π₃ ≅ homological_complex.eval C c j :=
nat_iso.of_components (λ X, X.X_next_iso hij)
(λ X Y f, begin
  dsimp,
  simp only [homological_complex.hom.next_eq f hij, assoc, iso.inv_hom_id, comp_id],
end)

instance (i : M) [has_colimits_of_shape J C] :
  preserves_colimits_of_shape J (short_complex.functor_homological_complex C c i) :=
begin
  apply preserves_colimits_of_shape_of_projections,
  { rcases h : c.prev i with _ | ⟨j, hij⟩,
    { exact preserves_colimits_of_shape_of_nat_iso
        (functor_homological_complex_π₁_iso_zero i h).symm, },
    { exact preserves_colimits_of_shape_of_nat_iso
        (functor_homological_complex_π₁_iso_eval i j hij).symm, }, },
  { exact (infer_instance : preserves_colimits_of_shape J (homological_complex.eval C c i)), },
  { rcases h : c.next i with _ | ⟨j, hij⟩,
    { exact preserves_colimits_of_shape_of_nat_iso
        (functor_homological_complex_π₃_iso_zero i h).symm, },
    { exact preserves_colimits_of_shape_of_nat_iso
        (functor_homological_complex_π₃_iso_eval i j hij).symm, }, },
end

end functor_homological_complex

section functor_homology

variables {C : Type*} [category.{v} C] [abelian C]
variables {M : Type*} {c : complex_shape M}
  {J : Type v} [small_category J] [is_filtered J]
  [has_colimits_of_shape J C]
  [preserves_finite_limits (limits.colim : (J ⥤ C) ⥤ C)]
  [preserves_finite_colimits (limits.colim : (J ⥤ C) ⥤ C)]

namespace homology_functor_preserves_colimit

variable (F : short_complex (J ⥤ C))

def iso_datum := homology_iso_datum.tautological' F.1.f F.1.g F.2

instance (j : J) : preserves_finite_limits ((evaluation J C).obj j) :=
⟨by { intro F, introI, introI, apply_instance, }⟩
instance (j : J) : preserves_finite_colimits ((evaluation J C).obj j) :=
⟨by { intro F, introI, introI, apply_instance, }⟩
instance (j : J) : functor.additive ((evaluation J C).obj j) := { }
instance colim_additive : functor.additive (colim : (J ⥤ C) ⥤ C) := { }

def iso_data (j : J) := (iso_datum F).apply_exact_functor ((evaluation J C).obj j)

def iso_datum₀ := (iso_datum F).apply_exact_functor (colim : (J ⥤ C) ⥤ C)

def sanity_check_K : colimit ((iso_datum F).K) ≅ (iso_datum₀ F).K := iso.refl _
def sanity_check_H : colimit ((iso_datum F).H) ≅ (iso_datum₀ F).H := iso.refl _
def sanity_check_H' : (iso_datum F).H ≅ _root_.homology F.1.f F.1.g F.2 := iso.refl _

def F₀ := functor_category_equivalence.functor.obj F

def e : (F₀ F) ⋙ homology_functor ≅ (iso_datum F).H := nat_iso.of_components
(λ j, ((iso_datum F).apply_exact_functor ((evaluation J C).obj j)).iso.symm)
sorry

end homology_functor_preserves_colimit

instance (F₀ : J ⥤ short_complex C) : preserves_colimit F₀ short_complex.homology_functor :=
⟨λ s hs, begin
  /- TODO: it would be better to reduce to the case `F₀` is `F₀ F` for some
    `(F : short_complex (J ⥤ C))` with the definitions above -/
  have e : s ≅ colimit_cocone.cocone F₀,
  { refine is_initial.unique_up_to_iso _ _,
    all_goals { equiv_rw (cocone.is_colimit_equiv_is_initial _).symm, },
    exacts [hs, (colimit_cocone F₀).is_colimit], },
  suffices : is_colimit (homology_functor.map_cocone (colimit_cocone.cocone F₀)),
  { exact is_colimit.of_iso_colimit this
      ((cocones.functoriality _ homology_functor).map_iso e.symm), },
  sorry,
end⟩

instance : preserves_colimits_of_shape J
  (short_complex.homology_functor : short_complex C ⥤ C) := ⟨λ F, infer_instance⟩

end functor_homology


end short_complex
