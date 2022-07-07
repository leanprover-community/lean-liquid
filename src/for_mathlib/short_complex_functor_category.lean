import for_mathlib.short_complex_projections
import for_mathlib.homology_map_datum

noncomputable theory

open category_theory category_theory.category category_theory.limits
open_locale zero_object

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

@[simps]
def functor_category_equivalence : short_complex (J ⥤ C) ≌ J ⥤ short_complex C :=
{ functor := functor_category_equivalence.functor,
  inverse := functor_category_equivalence.inverse,
  unit_iso := functor_category_equivalence.unit_iso,
  counit_iso := functor_category_equivalence.counit_iso,
  functor_unit_iso_comp' := functor_category_equivalence.functor_unit_iso_comp, }

@[simps]
def functor_lift {X Y Z : J ⥤ C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0) :
  J ⥤ short_complex C :=
functor_category_equivalence.functor.obj (mk f g h)

@[simps]
def ι_middle [has_zero_object C] : C ⥤ short_complex C :=
functor_lift (0 : 0 ⟶ 𝟭 C) (0 : 𝟭 C ⟶ 0) zero_comp

def ι_middle_homology_nat_iso {A : Type*} [category A] [abelian A] :
  𝟭 A ≅ ι_middle ⋙ homology_functor :=
nat_iso.of_components
(λ X, (homology_iso_datum.of_both_zeros _ _ rfl rfl).iso)
(λ X Y f, begin
  erw (homology_map_datum.of_both_are_zeros (ι_middle.map f) rfl rfl rfl rfl).homology_map_eq,
  erw iso.hom_inv_id_assoc,
  refl,
end)

@[simps]
def nat_trans_hom_mk {S₁ S₂ : J ⥤ short_complex C} (τ₁ : S₁ ⋙ π₁ ⟶ S₂ ⋙ π₁)
  (τ₂ : S₁ ⋙ π₂ ⟶ S₂ ⋙ π₂) (τ₃ : S₁ ⋙ π₃ ⟶ S₂ ⋙ π₃)
  (comm₁₂ : (𝟙 S₁) ◫ φ₁₂ ≫ τ₂ = τ₁ ≫ (𝟙 S₂) ◫ φ₁₂)
  (comm₂₃ : (𝟙 S₁) ◫ φ₂₃ ≫ τ₃ = τ₂ ≫ (𝟙 S₂) ◫ φ₂₃) :
  S₁ ⟶ S₂ :=
functor_category_equivalence.counit_iso.inv.app S₁ ≫
  functor_category_equivalence.functor.map (hom_mk τ₁ τ₂ τ₃ comm₁₂ comm₂₃) ≫
  functor_category_equivalence.counit_iso.hom.app S₂

@[simp, reassoc]
def nat_trans_hom_mk_comp {S₁ S₂ S₃ : J ⥤ short_complex C} (τ₁ : S₁ ⋙ π₁ ⟶ S₂ ⋙ π₁)
  (τ₂ : S₁ ⋙ π₂ ⟶ S₂ ⋙ π₂) (τ₃ : S₁ ⋙ π₃ ⟶ S₂ ⋙ π₃)
  (comm₁₂ : (𝟙 S₁) ◫ φ₁₂ ≫ τ₂ = τ₁ ≫ (𝟙 S₂) ◫ φ₁₂)
  (comm₂₃ : (𝟙 S₁) ◫ φ₂₃ ≫ τ₃ = τ₂ ≫ (𝟙 S₂) ◫ φ₂₃)
  (τ₁' : S₂ ⋙ π₁ ⟶ S₃ ⋙ π₁)
  (τ₂' : S₂ ⋙ π₂ ⟶ S₃ ⋙ π₂) (τ₃' : S₂ ⋙ π₃ ⟶ S₃ ⋙ π₃)
  (comm₁₂' : (𝟙 S₂) ◫ φ₁₂ ≫ τ₂' = τ₁' ≫ (𝟙 S₃) ◫ φ₁₂)
  (comm₂₃' : (𝟙 S₂) ◫ φ₂₃ ≫ τ₃' = τ₂' ≫ (𝟙 S₃) ◫ φ₂₃) :
  nat_trans_hom_mk τ₁ τ₂ τ₃ comm₁₂ comm₂₃ ≫
    nat_trans_hom_mk τ₁' τ₂' τ₃' comm₁₂' comm₂₃' =
    nat_trans_hom_mk (τ₁ ≫ τ₁') (τ₂ ≫ τ₂') (τ₃ ≫ τ₃')
    (by rw [← assoc, comm₁₂, assoc, comm₁₂', assoc])
    (by rw [← assoc, comm₂₃, assoc, comm₂₃', assoc]) :=
begin
  ext,
  all_goals
  { dsimp [functor_category_equivalence.counit_iso, nat_iso.of_components,
      functor_category_equivalence.counit_iso.obj,
      functor_category_equivalence.functor],
    erw [id_comp, id_comp, id_comp, comp_id, comp_id, comp_id], },
end

@[simp]
def nat_trans_hom_mk_id (S : J ⥤ short_complex C) :
  nat_trans_hom_mk (𝟙 (S ⋙ π₁)) (𝟙 (S ⋙ π₂)) (𝟙 (S ⋙ π₃))
  (by simp only [id_comp, comp_id]) (by simp only [id_comp, comp_id]) = 𝟙 S :=
begin
  ext,
  all_goals
  { dsimp [functor_category_equivalence.counit_iso, nat_iso.of_components,
      functor_category_equivalence.counit_iso.obj,
      functor_category_equivalence.functor],
    erw [id_comp, comp_id],
    refl, },
end

@[simps]
def functor_nat_iso_mk {S₁ S₂ : J ⥤ short_complex C} (τ₁ : S₁ ⋙ π₁ ≅ S₂ ⋙ π₁)
  (τ₂ : S₁ ⋙ π₂ ≅ S₂ ⋙ π₂) (τ₃ : S₁ ⋙ π₃ ≅ S₂ ⋙ π₃)
  (comm₁₂ : (𝟙 S₁) ◫ φ₁₂ ≫ τ₂.hom = τ₁.hom ≫ (𝟙 S₂) ◫ φ₁₂)
  (comm₂₃ : (𝟙 S₁) ◫ φ₂₃ ≫ τ₃.hom = τ₂.hom ≫ (𝟙 S₂) ◫ φ₂₃) :
  S₁ ≅ S₂ :=
begin
  have comm₁₂' : 𝟙 S₂ ◫ φ₁₂ ≫ τ₂.inv = τ₁.inv ≫ 𝟙 S₁ ◫ φ₁₂,
  { simpa only [← cancel_epi τ₁.hom, ← cancel_mono τ₂.hom, assoc, τ₂.inv_hom_id, comp_id,
      τ₁.hom_inv_id_assoc] using comm₁₂.symm, },
  have comm₂₃' : 𝟙 S₂ ◫ φ₂₃ ≫ τ₃.inv = τ₂.inv ≫ 𝟙 S₁ ◫ φ₂₃,
  { simpa only [← cancel_epi τ₂.hom, ← cancel_mono τ₃.hom, assoc, τ₃.inv_hom_id, comp_id,
      τ₂.hom_inv_id_assoc] using comm₂₃.symm, },
  exact
  { hom := nat_trans_hom_mk τ₁.hom τ₂.hom τ₃.hom comm₁₂ comm₂₃,
    inv := nat_trans_hom_mk τ₁.inv τ₂.inv τ₃.inv comm₁₂' comm₂₃',
    hom_inv_id' := by simp only [nat_trans_hom_mk_comp, iso.hom_inv_id, nat_trans_hom_mk_id],
    inv_hom_id' := by simp only [nat_trans_hom_mk_comp, iso.inv_hom_id, nat_trans_hom_mk_id], },
end

end short_complex
