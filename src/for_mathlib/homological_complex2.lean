import algebra.homology.additive
import category_theory.abelian.homology
import category_theory.preadditive.functor_category
import for_mathlib.abelian_sheaves.functor_category
import for_mathlib.homology_lift_desc

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

.

set_option pp.universes true

def eval_functor_homology_iso (F : X ⥤ homological_complex 𝒜 c) (i) :
  F ⋙ homology_functor _ c i ≅ (eval_functor.obj F).homology i :=
{ hom := homology.lift _ _ _
  { app := λ t, homology.desc' _ _ _ (kernel.ι ((F.obj t).d_from i) ≫ cokernel.π (((eval_functor.obj.{0 v u v v} F).d_to i).app t))
      begin
        rw [kernel.lift_ι_assoc],
        sorry
      end ≫ (nat_trans.cokernel_obj_iso.{u v v} _ t).inv,
    naturality' := begin
      intros, dsimp, sorry
    end }
    sorry,
  inv := homology.desc' _ _ _
  { app := λ t, (nat_trans.kernel_obj_iso.{u v v} _ t).hom ≫
      (homology.lift _ _ _
      (kernel.ι _ ≫ cokernel.π _) begin
        rw [category.assoc, cokernel.π_desc],
        sorry
      end),
    naturality' := sorry }
    sorry,
  hom_inv_id' := by { sorry; rw homology.lift_desc', },
  inv_hom_id' := sorry }

end homological_complex
