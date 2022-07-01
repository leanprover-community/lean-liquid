import for_mathlib.short_complex_projections

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {J C : Type*} [category J] [category C] [has_zero_morphisms C]

namespace short_complex

namespace functor_category_equivalence

instance evaluation_preserves_zero_morphisms
  (j : J) : ((evaluation J C).obj j).preserves_zero_morphisms := ⟨λ F G, rfl⟩

/- deterministic timeouts may occur if we add @[simps] attributes --/

def functor : short_complex (J ⥤ C) ⥤ J ⥤ short_complex C :=
functor.flip
{ obj := λ j, functor.map_short_complex ((evaluation J C).obj j),
  map := λ i j f, nat_trans.map_short_complex ((evaluation J C).map f), }

@[simps]
def inverse.obj (F : (J ⥤ short_complex C)) : short_complex (J ⥤ C) :=
mk ((𝟙 F) ◫ φ₁₂) ((𝟙 F) ◫ φ₂₃) begin
  ext,
  simp only [nat_trans.comp_app, nat_trans.hcomp_app, φ₁₂_app, nat_trans.id_app,
    π₂_map, φ₂₃_app, π₃_map, assoc, zero_app],
  erw [id_comp, comp_id],
  apply short_complex.zero,
end

@[simps]
def inverse.map {F G : (J ⥤ short_complex C)} (φ : F ⟶ G) : inverse.obj F ⟶ inverse.obj G :=
begin
  refine ⟨φ ◫ 𝟙 _, φ ◫ 𝟙 _, φ ◫ 𝟙 _, _, _⟩;
  ext; dsimp; erw [comp_id, id_comp, id_comp, comp_id],
  exacts [(φ.app x).comm₁₂, (φ.app x).comm₂₃],
end

def inverse : (J ⥤ short_complex C) ⥤ short_complex (J ⥤ C) :=
{ obj := inverse.obj,
  map := λ F G, inverse.map,
  map_id' := λ F, by { ext; apply comp_id, },
  map_comp' := λ F₁ F₂ F₃ φ ψ, by { ext; dsimp; erw [id_comp, id_comp, id_comp], }, }

def unit_iso.obj (S : short_complex (J ⥤ C)) : S ≅ (functor ⋙ inverse).obj S :=
begin
  refine iso_mk _ _ _ _ _;
  try { refine nat_iso.of_components (λ X, iso.refl _) _,
    intros i j f, dsimp, erw [comp_id, id_comp], refl, },
  all_goals { ext, dsimp [functor, inverse], erw [comp_id, id_comp], },
end

def unit_iso : 𝟭 (short_complex (J ⥤ C)) ≅
  functor_category_equivalence.functor ⋙ functor_category_equivalence.inverse :=
nat_iso.of_components unit_iso.obj
(λ S₁ S₂ ψ, begin
  ext;
  dsimp [iso_mk, nat_iso.of_components, iso_mk, functor, inverse, unit_iso.obj];
  erw [comp_id, id_comp, id_comp],
end)

def counit_iso.obj (F : J ⥤ short_complex C) : (inverse ⋙ functor).obj F ≅ F :=
nat_iso.of_components
(λ j, begin
  refine iso_mk (iso.refl _) (iso.refl _) (iso.refl _) _ _,
  all_goals { dsimp [functor, inverse], erw [id_comp, comp_id, comp_id], },
end)
(λ i j f, by { ext; dsimp; erw [comp_id, id_comp]; refl, })

def counit_iso : functor_category_equivalence.inverse ⋙
  functor_category_equivalence.functor ≅ 𝟭 (J ⥤ short_complex C) :=
nat_iso.of_components counit_iso.obj
(λ F₁ F₂ φ, by { ext; dsimp [functor, inverse, counit_iso.obj]; erw [id_comp, comp_id], })

lemma functor_unit_iso_comp (F : short_complex (J ⥤ C)) :
  functor_category_equivalence.functor.map (functor_category_equivalence.unit_iso.hom.app F) ≫
  functor_category_equivalence.counit_iso.hom.app (functor_category_equivalence.functor.obj F) =
  𝟙 _ :=
begin
  dsimp [functor_category_equivalence.functor, functor_category_equivalence.unit_iso,
    functor_category_equivalence.inverse, functor_category_equivalence.counit_iso,
    evaluation, functor.flip, functor.map_short_complex,
    functor_category_equivalence.counit_iso.obj,
    functor_category_equivalence.unit_iso.obj,
    nat_iso.of_components],
  ext;
  apply id_comp,
end

end functor_category_equivalence

def functor_category_equivalence : short_complex (J ⥤ C) ≌ J ⥤ short_complex C :=
{ functor := functor_category_equivalence.functor,
  inverse := functor_category_equivalence.inverse,
  unit_iso := functor_category_equivalence.unit_iso,
  counit_iso := functor_category_equivalence.counit_iso,
  functor_unit_iso_comp' := functor_category_equivalence.functor_unit_iso_comp, }

end short_complex
