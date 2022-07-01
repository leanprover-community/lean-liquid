import for_mathlib.short_complex

noncomputable theory

open category_theory category_theory.category category_theory.limits

namespace short_complex

variables {C : Type*} [category C] [has_zero_morphisms C]

@[simps]
def π₁ : short_complex C ⥤ C :=
{ obj := λ S, S.1.X,
  map := λ S₁ S₂ f, f.τ₁, }

@[simps]
def π₂ : short_complex C ⥤ C :=
{ obj := λ S, S.1.Y,
  map := λ S₁ S₂ f, f.τ₂, }

@[simps]
def π₃ : short_complex C ⥤ C :=
{ obj := λ S, S.1.Z,
  map := λ S₁ S₂ f, f.τ₃, }

@[simps]
def φ₁₂ : (π₁ : short_complex C ⥤ C) ⟶ π₂ :=
{ app := λ S, S.1.f,
  naturality' := λ S₁ S₂ f, (composable_morphisms.hom.comm₁₂ f).symm, }

@[simps]
def φ₂₃ : (π₂ : short_complex C ⥤ C) ⟶ π₃ :=
{ app := λ S, S.1.g,
  naturality' := λ S₁ S₂ f, (composable_morphisms.hom.comm₂₃ f).symm, }

section construction

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

end short_complex
