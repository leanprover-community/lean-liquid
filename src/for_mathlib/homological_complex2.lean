import algebra.homology.additive
import category_theory.abelian.homology
import category_theory.preadditive.functor_category
import for_mathlib.abelian_sheaves.functor_category
import for_mathlib.homology_lift_desc
import for_mathlib.has_homology
import for_mathlib.exact_functor

open category_theory category_theory.limits

namespace homological_complex

section
variables {ι X 𝒜 : Type*} [category X] [category 𝒜] [preadditive 𝒜] {c : complex_shape ι}

instance evaluation_additive (x : X) : ((evaluation X 𝒜).obj x).additive :=
{ map_add' := λ F G f g, by simp only [evaluation_obj_map, nat_trans.app_add] }

@[simps]
def functor_eval.obj (x : X) : homological_complex (X ⥤ 𝒜) c ⥤ homological_complex 𝒜 c :=
((evaluation X 𝒜).obj x).map_homological_complex _

@[simps]
def functor_eval : X ⥤ homological_complex (X ⥤ 𝒜) c ⥤ homological_complex 𝒜 c :=
{ obj := λ x, functor_eval.obj x,
  map := λ x y f,
  { app := λ C,
    { f := λ i, (C.X i).map f,
      comm' := λ _ _ _, nat_trans.naturality _ _ },
    naturality' := λ _ _ _, by { ext i, symmetry, apply nat_trans.naturality } },
  map_id' := by { intros, ext, dsimp, rw [category_theory.functor.map_id], },
  map_comp' := by { intros, ext, dsimp, rw [category_theory.functor.map_comp], } }

.

@[simps]
def eval_functor.obj (F : X ⥤ homological_complex 𝒜 c) : homological_complex (X ⥤ 𝒜) c :=
{ X := λ i, F ⋙ homological_complex.eval _ _ i,
  d := λ i j, whisker_left _ $
  { app := λ T, T.d _ _,
    naturality' := by { intros, dsimp, rw f.comm } },
  shape' := by { intros, ext, apply shape, assumption },
  d_comp_d' := by { intros, ext, apply d_comp_d } }

@[simps]
def eval_functor : (X ⥤ homological_complex 𝒜 c) ⥤ homological_complex (X ⥤ 𝒜) c :=
{ obj := λ F, eval_functor.obj F,
  map := λ F G η,
  { f := λ i, whisker_right η _,
    comm' := by { intros, ext, dsimp, rw (η.app _).comm } },
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }

def eval_functor_equiv : (X ⥤ homological_complex 𝒜 c) ≌ homological_complex (X ⥤ 𝒜) c :=
equivalence.mk
eval_functor
functor_eval.flip
(nat_iso.of_components (λ F, nat_iso.of_components (λ x,
  hom.iso_of_components (λ i, iso.refl _)
  (by { intros, simp only [iso.refl_hom, category.id_comp, category.comp_id], refl }))
  (by { intros, ext, dsimp, simp only [category.id_comp, category.comp_id] }))
  (by { intros, ext, dsimp, simp only [category.id_comp, category.comp_id] }))
(nat_iso.of_components (λ T, hom.iso_of_components
  (λ i, nat_iso.of_components (λ x, iso.refl _)
  (by { intros, simp only [iso.refl_hom, category.id_comp, category.comp_id], refl }))
  (by { intros, ext, dsimp, simp only [category.id_comp, category.comp_id] }))
  (by { intros, ext, dsimp, simp only [category.id_comp, category.comp_id] }))

end

universes v u
variables {ι : Type} {X : Type v} {𝒜 : Type u}
  [small_category X] [category.{v} 𝒜] [abelian 𝒜] {c : complex_shape ι}

noncomputable theory

instance (x : X) : preserves_finite_limits ((evaluation X 𝒜).obj x) :=
⟨by { intro J, introI, introI, apply limits.evaluation_preserves_limits_of_shape, }⟩

instance (x : X) : preserves_finite_colimits ((evaluation X 𝒜).obj x) :=
⟨by { intro J, introI, introI, apply limits.evaluation_preserves_colimits_of_shape, }⟩

def functor_eval_homology_iso (G : homological_complex (X ⥤ 𝒜) c) (i) :
  G.homology i ≅ functor_eval.flip.obj G ⋙ homology_functor _ c i :=
nat_iso.of_components (λ x, (functor.homology_functor_iso ((evaluation X 𝒜).obj x) c i).app G)
begin
  sorry,
end

def eval_functor_homology_iso (F : X ⥤ homological_complex 𝒜 c) (i) :
  F ⋙ homology_functor _ c i ≅ (eval_functor.obj F).homology i :=
iso_whisker_right (eval_functor_equiv.unit_iso.app F) (homology_functor 𝒜 c i)
  ≪≫ (functor_eval_homology_iso ((@eval_functor _ X 𝒜 _ _ _ c).obj F) i).symm

end homological_complex
