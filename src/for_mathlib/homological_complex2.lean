import algebra.homology.additive
import category_theory.abelian.homology
import category_theory.preadditive.functor_category
import for_mathlib.abelian_sheaves.functor_category
import for_mathlib.homology_lift_desc
import for_mathlib.has_homology

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

attribute [reassoc] homology.lift_desc'

def eval_functor_homology_iso (F : X ⥤ homological_complex 𝒜 c) (i) :
  F ⋙ homology_functor _ c i ≅ (eval_functor.obj F).homology i :=
{ hom := homology.lift _ _ _
  { app := λ t, homology.desc' _ _ _ (kernel.ι ((F.obj t).d_from i) ≫ cokernel.π (((eval_functor.obj.{0 v u v v} F).d_to i).app t))
      begin
        sorry {
        rw [kernel.lift_ι_assoc],
        by_cases hi : c.prev i = none,
        { rw [d_to_eq_zero _ hi, d_to_eq_zero _ hi, zero_comp], },
        rw [option.eq_none_iff_forall_not_mem, not_forall] at hi,
        obtain ⟨⟨j, hji⟩, -⟩ := hi,
        rw [d_to_eq _ hji, d_to_eq _ hji],
        have := cokernel.condition (((eval_functor.obj F).X_prev_iso hji).hom.app t ≫ (F.obj t).d j i),
        simp only [category.assoc, preadditive.is_iso.comp_left_eq_zero] at this ⊢,
        rwa [nat_trans.comp_app, eval_functor.obj_d, whisker_left_app],
        } -- !!! END OF SORRY BLOCK
      end ≫ (nat_trans.cokernel_obj_iso.{u v v} _ t).inv,
    naturality' := by sorry; begin
      intros x y f, dsimp only [functor.comp_map],
      ext,
      simp only [category.assoc],
      erw [homology.π'_map_assoc, homology.π'_desc'_assoc, homology.π'_desc'_assoc],
      simp only [category.assoc],
      have h1 := @nat_trans.cokernel_obj_iso_π_inv.{_ _ v} _ _ _ _ (_root_.id _) _ _ _ ((eval_functor.obj F).d_to i) y,
      have h2 := @nat_trans.cokernel_obj_iso_π_inv_assoc.{_ _ v} _ _ _ _ (_root_.id _) _ _ _ ((eval_functor.obj F).d_to i) x,
      erw [h1, h2],
      simp only [hom.sq_to_right, kernel.lift_ι_assoc, category.assoc, ← nat_trans.naturality],
      refl,
    end }
    begin
      sorry {
      ext t, dsimp only [nat_trans.comp_app, nat_trans.app_zero],
      simp only [homology.π'_desc'_assoc, category.assoc, comp_zero],
      have h1 := @nat_trans.cokernel_obj_iso_π_inv_assoc.{_ _ v} _ _ _ _ (_root_.id _) _ _ _ ((eval_functor.obj F).d_to i) t,
      erw h1,
      rw [← nat_trans.comp_app, cokernel.π_desc],
      by_cases hi : c.next i = none,
      { rw [d_from_eq_zero _ hi, d_from_eq_zero _ hi, nat_trans.app_zero, comp_zero], },
      rw [option.eq_none_iff_forall_not_mem, not_forall] at hi,
      obtain ⟨⟨j, hij⟩, -⟩ := hi,
      rw [d_from_eq _ hij, d_from_eq _ hij],
      have := kernel.condition ((F.obj t).d i j ≫ ((F.obj t).X_next_iso hij).inv),
      simp only [nat_trans.comp_app, ← category.assoc, preadditive.is_iso.comp_right_eq_zero] at this ⊢,
      rwa [eval_functor.obj_d, whisker_left_app],
      } -- !!! END OF SORRY BLOCK
    end,
  inv := homology.desc' _ _ _
  { app := λ t, (nat_trans.kernel_obj_iso.{u v v} _ t).hom ≫
      (homology.lift _ _ _
      (kernel.ι _ ≫ cokernel.π _) begin
        sorry {
        rw [category.assoc, cokernel.π_desc],
        by_cases hi : c.next i = none,
        { rw [d_from_eq_zero _ hi, d_from_eq_zero _ hi, comp_zero], },
        rw [option.eq_none_iff_forall_not_mem, not_forall] at hi,
        obtain ⟨⟨j, hij⟩, -⟩ := hi,
        rw [d_from_eq _ hij, d_from_eq _ hij],
        have := kernel.condition (((eval_functor.obj F).d i j ≫ ((eval_functor.obj F).X_next_iso hij).inv).app t),
        simp only [nat_trans.comp_app, ← category.assoc, preadditive.is_iso.comp_right_eq_zero] at this ⊢,
        rwa [eval_functor.obj_d],
        } -- !!! END OF SORRY BLOCK
      end),
    naturality' := by sorry; begin
      intros x y f, dsimp only [functor.comp_map],
      ext,
      simp only [category.assoc],
      erw [homology.lift_ι, homology.map_ι, homology.lift_ι_assoc],
      simp only [category.assoc],
      have h1 := @nat_trans.kernel_obj_iso_hom_ι_assoc.{_ _ v} _ _ _ _ (_root_.id _) _ _ _ ((eval_functor.obj F).d_from i) x,
      have h2 := @nat_trans.kernel_obj_iso_hom_ι_assoc.{_ _ v} _ _ _ _ (_root_.id _) _ _ _ ((eval_functor.obj F).d_from i) y,
      erw [h1, h2],
      simp only [arrow.w_mk_right, arrow.mk_hom, eq_self_iff_true, nat_trans.naturality_assoc,
        hom.sq_from_left, hom.sq_to_left, cokernel.π_desc],
      refl,
    end }
    begin
      sorry {
      ext t, dsimp only [nat_trans.comp_app, nat_trans.app_zero],
      simp only [homology.lift_ι, category.assoc, zero_comp],
      have h1 := @nat_trans.kernel_obj_iso_hom_ι_assoc.{_ _ v} _ _ _ _ (_root_.id _) _ _ _ ((eval_functor.obj F).d_from i) t,
      erw h1,
      rw [← category.assoc, ← nat_trans.comp_app, kernel.lift_ι],
      by_cases hi : c.prev i = none,
      { rw [d_to_eq_zero _ hi, d_to_eq_zero _ hi, nat_trans.app_zero, zero_comp], },
      rw [option.eq_none_iff_forall_not_mem, not_forall] at hi,
      obtain ⟨⟨j, hji⟩, -⟩ := hi,
      rw [d_to_eq _ hji, d_to_eq _ hji],
      have := cokernel.condition (((F.obj t).X_prev_iso hji).hom ≫ (F.obj t).d j i),
      simp only [nat_trans.comp_app, category.assoc, preadditive.is_iso.comp_left_eq_zero] at this ⊢,
      rwa [eval_functor.obj_d, whisker_left_app],
      } -- !!! END OF SORRY BLOCK
    end,
  hom_inv_id' := begin
    let φ : (eval_functor.obj F).X i ⟶ F ⋙ homology_functor 𝒜 c i :=
      ⟨λ x, homology.lift _ _ _ (cokernel.π ((F.obj x).d_to i)) _, _⟩,
    let ψ : F ⋙ homology_functor 𝒜 c i ⟶ (eval_functor.obj F).X i :=
      ⟨λ x, homology.desc' _ _ _ (kernel.ι ((F.obj x).d_from i)) _, _⟩,
    rw homology.lift_desc' _ _ _ _ _ _ _ φ _ _ ψ,
    { sorry },
    { sorry },
    { ext x, dsimp only [nat_trans.comp_app],
      have := @nat_trans.cokernel_obj_iso_π_inv.{_ _ v} _ _ _ _ (_root_.id _) _ _ _ ((eval_functor.obj F).d_to i) x,
      rw [homology.π'_desc'_assoc, homology.π'_desc'_assoc, category.assoc, this], },
    { ext x, dsimp only [nat_trans.comp_app],
      have := @nat_trans.kernel_obj_iso_hom_ι_assoc.{_ _ v} _ _ _ _ (_root_.id _) _ _ _ ((eval_functor.obj F).d_from i) x,
      rw [category.assoc, homology.lift_ι, category.assoc, homology.lift_ι, this], },
    { sorry },
    { sorry },
    { sorry },
    recover, all_goals { sorry },
  end,
  inv_hom_id' := by sorry; begin
    ext : 2,
    simp only [category.assoc, homology.π'_desc'_assoc, homology.lift_ι,
      category.id_comp, category.comp_id],
    ext x,
    simp only [nat_trans.comp_app, category.assoc],
    rw [homology.lift_desc'_assoc _ _ _ _ _ _ _
      (cokernel.π (((eval_functor.obj F).d_to i).app x)) _ _
      (kernel.ι (((eval_functor.obj F).d_from i).app x))],
    { have h1 := @nat_trans.kernel_obj_iso_hom_ι_assoc.{_ _ v} _ _ _ _ (_root_.id _) _ _ _ ((eval_functor.obj F).d_from i) x,
      have h2 := @nat_trans.cokernel_obj_iso_π_inv.{_ _ v} _ _ _ _ (_root_.id _) _ _ _ ((eval_functor.obj F).d_to i) x,
      erw [h1, h2],
      rw [← nat_trans.comp_app, ← nat_trans.comp_app], congr' 1,
      symmetry,
      apply (homology.has _ _ _).π_ι, },
    { by_cases hi : c.next i = none,
      { rw [d_from_eq_zero _ hi, d_from_eq_zero _ hi, nat_trans.app_zero, comp_zero], },
      rw [option.eq_none_iff_forall_not_mem, not_forall] at hi,
      obtain ⟨⟨j, hij⟩, -⟩ := hi,
      have := kernel.condition (((eval_functor.obj F).d_from i).app x),
      rw [d_from_eq _ hij] at this ⊢,
      rw [d_from_eq _ hij],
      simp only [nat_trans.comp_app, ← category.assoc, preadditive.is_iso.comp_right_eq_zero] at this ⊢,
      rwa [eval_functor.obj_d] at this, },
    { refl },
    { refl },
    { by_cases hi : c.prev i = none,
      { rw [d_to_eq_zero _ hi, d_to_eq_zero _ hi, nat_trans.app_zero, zero_comp], },
      rw [option.eq_none_iff_forall_not_mem, not_forall] at hi,
      obtain ⟨⟨j, hji⟩, -⟩ := hi,
      have := cokernel.condition (((eval_functor.obj F).d_to i).app x),
      rw [d_to_eq _ hji] at this ⊢,
      rw [d_to_eq _ hji],
      simp only [nat_trans.comp_app, category.assoc, preadditive.is_iso.comp_left_eq_zero] at this ⊢,
      rwa [eval_functor.obj_d] at this, },
  end }

end homological_complex
