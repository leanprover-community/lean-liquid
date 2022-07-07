import breen_deligne.eval2
import condensed.tensor
import condensed.evaluation_homology
import condensed.sheafification_homology
import for_mathlib.AddCommGroup
import for_mathlib.map_to_sheaf_is_iso
import condensed.is_iso_iff_extrdisc
import condensed.ab5
import condensed.ab4
import for_mathlib.endomorphisms.ab4
import for_mathlib.homology_exact
import for_mathlib.free_abelian_group2
import for_mathlib.embed_preserves_colimits

.

noncomputable theory

universes u

open category_theory category_theory.limits breen_deligne opposite
open bounded_homotopy_category

abbreviation freeCond' := Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_Condensed_Ab

namespace Condensed

variables (BD : package)

abbreviation freeFunc : (Profiniteᵒᵖ ⥤ Ab) ⥤ Profiniteᵒᵖ ⥤ Ab :=
(whiskering_right _ _ _).obj (forget _ ⋙ AddCommGroup.free)

namespace eval_freeCond'_iso

def component_zero (M : Condensed.{u} Ab.{u+1}) :
  ((BD.eval' freeCond').obj M).X (int.of_nat 0) ≅
  ((presheaf_to_Condensed_Ab.map_homological_complex (complex_shape.up ℤ)).obj
    ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))).X
  (int.of_nat 0) :=
presheaf_to_Condensed_Ab.map_iso begin
    refine functor.associator _ _ _ ≪≫ _,
    refine iso_whisker_right _ _,
    refine (Condensed_Ab_to_presheaf.map_biproduct _),
  end

def component_pos (M : Condensed.{u} Ab.{u+1}) (i : ℕ) :
  ((BD.eval' freeCond').obj M).X (int.of_nat (i+1)) ≅
  ((presheaf_to_Condensed_Ab.map_homological_complex (complex_shape.up ℤ)).obj
    ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))).X
  (int.of_nat (i+1)) :=
is_zero.iso (is_zero_zero _) (functor.map_is_zero _ $ is_zero_zero _)

def component_neg (M : Condensed.{u} Ab.{u+1}) (i : ℕ) :
  ((BD.eval' freeCond').obj M).X (-[1+i]) ≅
  ((presheaf_to_Condensed_Ab.map_homological_complex (complex_shape.up ℤ)).obj
    ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))).X
  (-[1+i]) :=
presheaf_to_Condensed_Ab.map_iso begin
    refine functor.associator _ _ _ ≪≫ _,
    refine iso_whisker_right _ _,
    refine (Condensed_Ab_to_presheaf.map_biproduct _),
  end

end eval_freeCond'_iso

open_locale big_operators
open category_theory.preadditive

lemma eval_freeCond'_iso_component_aux₀ (M : Condensed.{u} Ab.{u+1}) :
  (eval_freeCond'_iso.component_neg BD M 0).hom ≫
    ((presheaf_to_Condensed_Ab.map_homological_complex (complex_shape.up ℤ)).obj
       ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))).d
      -[1+ 0] (int.of_nat 0) =
  ((BD.eval' freeCond').obj M).d -[1+ 0] (int.of_nat 0) ≫
  (eval_freeCond'_iso.component_zero BD M).hom :=
begin
  dsimp [eval_freeCond'_iso.component_neg, eval_freeCond'_iso.component_zero, package.eval',
    homological_complex.embed, homological_complex.embed.obj],
  erw homological_complex.embed.d_some_some,
  erw homological_complex.embed.d_some_some,
  dsimp [data.eval_functor', universal_map.eval_Pow],
  simp_rw free_abelian_group.lift_eq_sum,
  simp only [nat_trans.app_sum, nat_trans.app_zsmul],
  --dsimp,
  rw [functor.map_sum, sum_comp, comp_sum],
  refine finset.sum_congr rfl _, rintro x -,
  rw [functor.map_zsmul, zsmul_comp, comp_zsmul],
  refine congr_arg2 _ rfl _,
  dsimp,
  rw ← presheaf_to_Condensed_Ab.map_comp,
  erw ← presheaf_to_Condensed_Ab.map_comp,
  congr' 1,
  ext t : 2, dsimp only [nat_trans.comp_app, whisker_right_app, functor.associator],
  simp only [category.id_comp, category.comp_id],
  simp only [← functor.map_comp],
  congr' 1, simp only [← nat_trans.comp_app], congr' 1,
  apply biproduct.hom_ext, intros j,
  simp only [category.assoc, biproduct.matrix_π, biproduct.lift_π],
  dsimp only [functor.map_bicone],
  rw biproduct.lift_desc,
  erw [← Condensed_Ab_to_presheaf.map_comp, biproduct.matrix_π],
  simp_rw [comp_zsmul, category.comp_id, ← functor.map_zsmul, ← functor.map_sum],
  congr' 1,
  apply biproduct.hom_ext', intros k,
  rw [biproduct.ι_desc, comp_sum],
  rw finset.sum_eq_single_of_mem k (finset.mem_univ _),
  { simp },
  { rintros b - hb, dsimp, rw comp_zsmul, rw biproduct.ι_π,
    rw [dif_neg hb.symm, zsmul_zero] }
end

lemma eval_freeCond'_iso_component_aux_i (M : Condensed.{u} Ab.{u+1}) (i : ℕ) :
(eval_freeCond'_iso.component_neg BD M (i+1)).hom ≫
    ((presheaf_to_Condensed_Ab.map_homological_complex (complex_shape.up ℤ)).obj
       ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))).d
      -[1+ (i+1)] -[1+ i] =
  ((BD.eval' freeCond').obj M).d -[1+ (i+1)] -[1+ i] ≫
  (eval_freeCond'_iso.component_neg BD M i).hom :=
begin
  dsimp [eval_freeCond'_iso.component_neg, eval_freeCond'_iso.component_zero, package.eval',
    homological_complex.embed, homological_complex.embed.obj],
  erw homological_complex.embed.d_some_some,
  erw homological_complex.embed.d_some_some,
  dsimp [data.eval_functor', universal_map.eval_Pow],
  simp_rw free_abelian_group.lift_eq_sum,
  simp only [nat_trans.app_sum, nat_trans.app_zsmul],
  --dsimp,
  rw [functor.map_sum, sum_comp, comp_sum],
  refine finset.sum_congr rfl _, rintro x -,
  rw [functor.map_zsmul, zsmul_comp, comp_zsmul],
  refine congr_arg2 _ rfl _,
  dsimp,
  rw ← presheaf_to_Condensed_Ab.map_comp,
  erw ← presheaf_to_Condensed_Ab.map_comp,
  congr' 1,
  ext t : 2, dsimp only [nat_trans.comp_app, whisker_right_app, functor.associator],
  simp only [category.id_comp, category.comp_id],
  simp only [← functor.map_comp],
  congr' 1, simp only [← nat_trans.comp_app], congr' 1,
  apply biproduct.hom_ext, intros j,
  simp only [category.assoc, biproduct.matrix_π, biproduct.lift_π],
  dsimp only [functor.map_bicone],
  rw biproduct.lift_desc,
  erw [← Condensed_Ab_to_presheaf.map_comp, biproduct.matrix_π],
  simp_rw [comp_zsmul, category.comp_id, ← functor.map_zsmul, ← functor.map_sum],
  congr' 1,
  apply biproduct.hom_ext', intros k,
  rw [biproduct.ι_desc, comp_sum],
  rw finset.sum_eq_single_of_mem k (finset.mem_univ _),
  { simp },
  { rintros b - hb, dsimp, rw comp_zsmul, rw biproduct.ι_π,
    rw [dif_neg hb.symm, zsmul_zero] }
end

def eval_freeCond'_iso_component (M : Condensed.{u} Ab.{u+1}) :
  ((BD.eval' freeCond').obj M) ≅
  (presheaf_to_Condensed_Ab.map_homological_complex _).obj
  ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M)) :=
homological_complex.hom.iso_of_components
(λ i,
match i with
| int.of_nat 0 := eval_freeCond'_iso.component_zero _ _
| int.of_nat (i+1) := eval_freeCond'_iso.component_pos _ _ _
| -[1+i] := eval_freeCond'_iso.component_neg _ _ _
end )
begin
  rintros ((_|i)|(_|i)) ((_|j)|(_|j)) ⟨rfl⟩,
  { apply is_zero.eq_of_tgt,
    apply functor.map_is_zero,
    apply is_zero_zero },
  { apply is_zero.eq_of_tgt,
    apply functor.map_is_zero,
    apply is_zero_zero },
  { apply eval_freeCond'_iso_component_aux₀ },
  { apply eval_freeCond'_iso_component_aux_i },
  { apply eval_freeCond'_iso_component_aux_i },
end
.

lemma eval_freeCond'_iso_component_hom_zero (M : Condensed.{u} Ab.{u+1}) :
  (eval_freeCond'_iso_component BD M).hom.f 0 =
  begin
    refine presheaf_to_Condensed_Ab.map _,
    refine _ ≫ (functor.associator _ _ _).hom,
    refine whisker_right _ _,
    refine whisker_right _ _,
    refine (Condensed_Ab_to_presheaf.map_biproduct _).hom,
  end := rfl

lemma eval_freeCond'_iso_component_hom_neg (M : Condensed.{u} Ab.{u+1}) (i : ℕ) :
  (eval_freeCond'_iso_component BD M).hom.f (-[1+i]) =
  begin
    refine presheaf_to_Condensed_Ab.map _,
    refine _ ≫ (functor.associator _ _ _).hom,
    refine whisker_right _ _,
    refine whisker_right _ _,
    refine (Condensed_Ab_to_presheaf.map_biproduct _).hom,
  end := rfl

namespace eval_freeAb_iso

def component_zero (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) :
  ((((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
  (op S.val)).map_homological_complex (complex_shape.up ℤ)).obj
  ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))).X (int.of_nat 0) ≅
  ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj (M.val.obj (op S.val))).X
  (int.of_nat 0) :=
begin
  refine AddCommGroup.free.map_iso _,
  refine (category_theory.forget _).map_iso _,
  refine ((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op S.val)).map_biproduct _
end

def component_pos (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) (i : ℕ) :
  ((((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
    (op S.val)).map_homological_complex (complex_shape.up ℤ)).obj
    ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))).X
    (int.of_nat (i + 1)) ≅
  ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj
  (M.val.obj (op S.val))).X (int.of_nat (i + 1)) :=
is_zero.iso (functor.map_is_zero _ $ is_zero_zero _) (is_zero_zero _)

def component_neg (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) (i : ℕ) :
  ((((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op S.val)).map_homological_complex
    (complex_shape.up ℤ)).obj
    ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))).X -[1+ i] ≅
  ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj (M.val.obj (op S.val))).X -[1+ i] :=
begin
  refine AddCommGroup.free.map_iso _,
  refine (category_theory.forget _).map_iso _,
  refine ((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op S.val)).map_biproduct _
end

end eval_freeAb_iso

local attribute [-simp] forget_map_eq_coe

lemma eval_freeAb_iso_component_aux₀ (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) :
  (eval_freeAb_iso.component_neg BD M S 0).hom ≫
    ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj (M.val.obj (op S.val))).d
      -[1+ 0] (int.of_nat 0) =
  ((((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op S.val)).map_homological_complex
    (complex_shape.up ℤ)).obj
      ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))).d -[1+ 0] (int.of_nat 0) ≫
  (eval_freeAb_iso.component_zero BD M S).hom :=
begin
  dsimp only [eval_freeAb_iso.component_neg, eval_freeAb_iso.component_zero, functor.map_iso,
    package.eval', data.eval_functor', functor.map_homological_complex,
    category_theory.evaluation, functor.comp_obj, homological_complex.embed,
    homological_complex.embed.obj],
  erw homological_complex.embed.d_some_some,
  erw homological_complex.embed.d_some_some,
  dsimp only [data.eval_functor, data.eval_functor', functor.comp_obj, functor.flip,
    homological_complex.functor_eval, homological_complex.functor_eval.obj,
    category_theory.evaluation, functor.map_homological_complex,
    universal_map.eval_Pow_functor, universal_map.eval_Pow, functor.map_biproduct],
  simp only [free_abelian_group.lift_eq_sum, sum_comp, comp_sum, nat_trans.app_sum],
  apply finset.sum_congr rfl, rintro x -,
  simp only [nat_trans.app_zsmul],
  dsimp [functor.map_bicone],
  simp only [zsmul_comp, comp_zsmul, ← functor.map_comp], congr' 3,
  apply biproduct.hom_ext, intros j,
  simp only [category.assoc, biproduct.lift_π, biproduct.matrix_π, biproduct.lift_desc],
  erw biproduct.lift_π,
  rw [← nat_trans.comp_app, biproduct.matrix_π],
  simp_rw [← nat_trans.id_app, ← nat_trans.app_zsmul, ← nat_trans.comp_app,
    ← nat_trans.app_sum], congr' 1,
  apply biproduct.hom_ext', intro k, simp only [comp_sum, biproduct.ι_desc],
  rw [finset.sum_eq_single_of_mem k (finset.mem_univ _),
  biproduct.ι_π_assoc, dif_pos rfl],
  { simpa, },
  { rintros b - hb, rw [biproduct.ι_π_assoc, dif_neg hb.symm, zero_comp] }
end

lemma eval_freeAb_iso_component_aux (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) (i : ℕ) :
  (eval_freeAb_iso.component_neg BD M S (i+1)).hom ≫
    ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (M.val.obj (op S.val))).d -[1+ (i+1)] -[1+ i] =
  ((((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
    (op S.val)).map_homological_complex (complex_shape.up ℤ)).obj
       ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))).d -[1+ (i+1)] -[1+ i] ≫
    (eval_freeAb_iso.component_neg BD M S i).hom :=
begin
  dsimp only [eval_freeAb_iso.component_neg, eval_freeAb_iso.component_zero, functor.map_iso,
    package.eval', data.eval_functor', functor.map_homological_complex,
    category_theory.evaluation, functor.comp_obj, homological_complex.embed,
    homological_complex.embed.obj],
  erw homological_complex.embed.d_some_some,
  erw homological_complex.embed.d_some_some,
  dsimp only [data.eval_functor, data.eval_functor', functor.comp_obj, functor.flip,
    homological_complex.functor_eval, homological_complex.functor_eval.obj,
    category_theory.evaluation, functor.map_homological_complex,
    universal_map.eval_Pow_functor, universal_map.eval_Pow, functor.map_biproduct],
  simp only [free_abelian_group.lift_eq_sum, sum_comp, comp_sum, nat_trans.app_sum],
  apply finset.sum_congr rfl, rintro x -,
  simp only [nat_trans.app_zsmul],
  dsimp [functor.map_bicone],
  simp only [zsmul_comp, comp_zsmul, ← functor.map_comp], congr' 3,
  apply biproduct.hom_ext, intros j,
  simp only [category.assoc, biproduct.lift_π, biproduct.matrix_π, biproduct.lift_desc],
  erw biproduct.lift_π,
  rw [← nat_trans.comp_app, biproduct.matrix_π],
  simp_rw [← nat_trans.id_app, ← nat_trans.app_zsmul, ← nat_trans.comp_app,
    ← nat_trans.app_sum], congr' 1,
  apply biproduct.hom_ext', intro k, simp only [comp_sum, biproduct.ι_desc],
  rw [finset.sum_eq_single_of_mem k (finset.mem_univ _),
  biproduct.ι_π_assoc, dif_pos rfl],
  { simpa, },
  { rintros b - hb, rw [biproduct.ι_π_assoc, dif_neg hb.symm, zero_comp] }
end

def eval_freeAb_iso_component (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) :
  (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op S.val)).map_homological_complex
    (complex_shape.up ℤ)).obj
  ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M)) ≅
  (BD.eval' $ category_theory.forget _ ⋙ AddCommGroup.free).obj (M.val.obj (op S.val)) :=
homological_complex.hom.iso_of_components
(λ i,
match i with
| int.of_nat 0 :=  eval_freeAb_iso.component_zero _ _ _
| int.of_nat (i+1) := eval_freeAb_iso.component_pos _ _ _ _
| -[1+i] := eval_freeAb_iso.component_neg _ _ _ _
end )
begin
  rintros ((_|i)|(_|i)) ((_|j)|(_|j)) ⟨rfl⟩,
  { apply is_zero.eq_of_tgt,
    apply is_zero_zero },
  { apply is_zero.eq_of_tgt,
    apply is_zero_zero },
  { apply eval_freeAb_iso_component_aux₀ },
  { apply eval_freeAb_iso_component_aux },
  { apply eval_freeAb_iso_component_aux },
end
.

@[simp]
lemma eval_freeAb_iso_component_zero (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) :
  (eval_freeAb_iso_component BD M S).hom.f 0 =
  (eval_freeAb_iso.component_zero BD M S).hom := rfl

@[simp]
lemma eval_freeAb_iso_component_neg (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) (i : ℕ) :
  (eval_freeAb_iso_component BD M S).hom.f (-[1+i]) =
  (eval_freeAb_iso.component_neg BD M S i).hom := rfl

lemma eval_freeCond'_iso_aux_zero
  (X Y : Condensed Ab) (f : X ⟶ Y) :
  ((BD.eval' freeCond').map f ≫ (eval_freeCond'_iso_component BD Y).hom).f (int.of_nat 0) =
  ((eval_freeCond'_iso_component BD X).hom ≫
     (Condensed_Ab_to_presheaf ⋙
        BD.eval' freeFunc ⋙ presheaf_to_Condensed_Ab.map_homological_complex
        (complex_shape.up ℤ)).map f).f (int.of_nat 0) :=
begin
  dsimp only [
    homological_complex.hom.iso_of_components,
    homological_complex.comp_f, package.eval', data.eval_functor', data.eval_functor,
    functor.comp_map, int.of_nat_zero,
    homological_complex.embed_nat_obj_down_up_zero_f,
    homological_complex.comp_f, functor.map_homological_complex_map_f,
    functor.comp_obj, functor.flip,
    homological_complex.functor_eval, universal_map.eval_Pow_functor,
    functor.map_homological_complex],
  rw eval_freeCond'_iso_component_hom_zero,
  rw eval_freeCond'_iso_component_hom_zero,
  dsimp,
  rw ← presheaf_to_Condensed_Ab.map_comp,
  erw ← presheaf_to_Condensed_Ab.map_comp,
  congr' 1, -- we got rid of the sheafification :)
  ext t : 2,
  dsimp,
  simp only [category.id_comp, category.comp_id, ← functor.map_comp],
  congr' 2,
  simp_rw ← nat_trans.comp_app, congr' 1,
  dsimp [functor.map_bicone],
  apply biproduct.hom_ext, intros j,
  simp only [category.assoc, biproduct.map_π, biproduct.lift_π_assoc, biproduct.lift_π],
  erw [← Condensed_Ab_to_presheaf.map_comp, ← Condensed_Ab_to_presheaf.map_comp,
    biproduct.map_π],
end

.

lemma eval_freeAb_iso_component_naturality (M : Condensed.{u} Ab.{u+1}) (S T : ExtrDisc.{u})
  (f : S ⟶ T) :
  (eval_freeAb_iso_component BD M T).hom ≫
  (BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).map
    (M.val.map (ExtrDisc_to_Profinite.map f).op) =
  (nat_trans.map_homological_complex ((category_theory.evaluation Profiniteᵒᵖ Ab).map f.val.op)
  (complex_shape.up ℤ)).app ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))
    ≫ (eval_freeAb_iso_component BD M S).hom :=
begin
  ext ((_|i)|i) : 2,
  { dsimp [eval_freeAb_iso.component_zero, package.eval'],
    simp only [← functor.map_comp], congr' 2,
    apply biproduct.hom_ext, intro j,
    dsimp [functor.map_bicone],
    simp only [category.assoc],
    erw biproduct.lift_π,
    erw biproduct.lift_π,
    erw biproduct.lift_π_assoc,
    dsimp,
    simp only [nat_trans.naturality],
    refl },
  { apply is_zero.eq_of_tgt,
    apply is_zero_zero },
  { dsimp [eval_freeAb_iso.component_neg, package.eval'],
    simp only [← functor.map_comp], congr' 2,
    apply biproduct.hom_ext, intro j,
    dsimp [functor.map_bicone],
    simp only [category.assoc],
    erw biproduct.lift_π,
    erw biproduct.lift_π,
    erw biproduct.lift_π_assoc,
    dsimp,
    simp only [nat_trans.naturality],
    refl },
end

lemma eval_freeCond'_iso_aux_neg
  (X Y : Condensed Ab) (f : X ⟶ Y) (i : ℕ) :
  ((BD.eval' freeCond').map f ≫ (eval_freeCond'_iso_component BD Y).hom).f (-[1+i]) =
  ((eval_freeCond'_iso_component BD X).hom ≫
     (Condensed_Ab_to_presheaf ⋙
        BD.eval' freeFunc ⋙ presheaf_to_Condensed_Ab.map_homological_complex
        (complex_shape.up ℤ)).map f).f (-[1+i]) :=
begin
  dsimp only [
    homological_complex.hom.iso_of_components,
    homological_complex.comp_f, package.eval', data.eval_functor', data.eval_functor,
    functor.comp_map, int.of_nat_zero,
    homological_complex.embed_nat_obj_down_up_zero_f,
    homological_complex.comp_f, functor.map_homological_complex_map_f,
    functor.comp_obj, functor.flip,
    homological_complex.functor_eval, universal_map.eval_Pow_functor,
    functor.map_homological_complex],
  rw eval_freeCond'_iso_component_hom_neg,
  rw eval_freeCond'_iso_component_hom_neg,
  dsimp,
  rw ← presheaf_to_Condensed_Ab.map_comp,
  erw ← presheaf_to_Condensed_Ab.map_comp,
  congr' 1, -- we got rid of the sheafification :)
  ext t : 2,
  dsimp,
  simp only [category.id_comp, category.comp_id, ← functor.map_comp],
  congr' 2,
  simp_rw ← nat_trans.comp_app, congr' 1,
  dsimp [functor.map_bicone],
  apply biproduct.hom_ext, intros j,
  simp only [category.assoc, biproduct.map_π, biproduct.lift_π_assoc, biproduct.lift_π],
  erw [← Condensed_Ab_to_presheaf.map_comp, ← Condensed_Ab_to_presheaf.map_comp,
    biproduct.map_π],
end

def eval_freeCond'_iso :
  BD.eval' freeCond' ≅
  Condensed_Ab_to_presheaf ⋙ BD.eval' freeFunc ⋙ presheaf_to_Condensed_Ab.map_homological_complex _ :=
nat_iso.of_components
(λ M, eval_freeCond'_iso_component _ _)
begin
  intros X Y f,
  ext ((_|i)|i) : 2,
  { apply eval_freeCond'_iso_aux_zero },
  { apply is_zero.eq_of_src, apply is_zero_zero },
  { apply eval_freeCond'_iso_aux_neg },
end

def eval_freeAb_iso (S : ExtrDisc.{u}) :
  Condensed_Ab_to_presheaf ⋙ BD.eval' freeFunc ⋙
  ((category_theory.evaluation _ _).obj (op S.val)).map_homological_complex _ ≅
  evaluation _ S.val ⋙ BD.eval' (category_theory.forget _ ⋙ AddCommGroup.free) :=
nat_iso.of_components
(λ M, eval_freeAb_iso_component _ _ _)
begin
  intros X Y f,
  ext ((_|i)|i) : 2,
  { dsimp [eval_freeAb_iso.component_zero, package.eval'],
    simp only [← functor.map_comp], congr' 2,
    apply biproduct.hom_ext, intros j,
    dsimp [functor.map_bicone],
    simp only [category.assoc, biproduct.map_π, biproduct.lift_π],
    erw biproduct.lift_π_assoc,
    erw biproduct.lift_π,
    simp_rw [← nat_trans.comp_app, biproduct.map_π],
    refl },
  { apply is_zero.eq_of_tgt, apply is_zero_zero },
  { dsimp [eval_freeAb_iso.component_neg, package.eval'],
    simp only [← functor.map_comp], congr' 2,
    apply biproduct.hom_ext, intros j,
    dsimp [functor.map_bicone],
    simp only [category.assoc, biproduct.map_π, biproduct.lift_π],
    erw biproduct.lift_π_assoc,
    erw biproduct.lift_π,
    simp_rw [← nat_trans.comp_app, biproduct.map_π],
    refl }
end

-- Move this.
def point {A : Type u} (a : A) : punit.{u+1} ⟶ A := λ _, a

def tensor_to_unsheafified_homology_component_applied
  (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S : ExtrDisc.{u}) (m : M.val.obj (op S.val)) :
  ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as.homology i ⟶
  (homological_complex.homology ((BD.eval' freeFunc).obj
    (Condensed_Ab_to_presheaf.obj M)) i).obj (op S.val) :=
(homotopy_category.homology_functor _ _ _).map
    ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).map
      ((AddCommGroup.adj.hom_equiv _ _).symm (point m))) ≫
      (homology_functor _ _ _).map (eval_freeAb_iso_component _ _ _).inv ≫
    (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
      (op S.val)).homology_functor_iso _ _).inv.app _

/-
match i with
| (int.of_nat 0) := (homotopy_category.homology_functor _ _ _).map
    ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).map
      ((AddCommGroup.adj.hom_equiv _ _).symm (point m))) ≫
      (homology_functor _ _ _).map (eval_freeAb_iso_component _ _ _).inv ≫
    (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
      (op S.val)).homology_functor_iso _ _).inv.app _
| (int.of_nat (i+1)) := 0
| (int.neg_succ_of_nat i) := (homotopy_category.homology_functor _ _ _).map
    ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).map
      ((AddCommGroup.adj.hom_equiv _ _).symm (point m))) ≫
      (homology_functor _ _ _).map (eval_freeAb_iso_component _ _ _).inv ≫
    (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
      (op S.val)).homology_functor_iso _ _).inv.app _
end
.

lemma tensor_to_unsheafified_homology_component_applied_eq
  (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S : ExtrDisc.{u}) (m : M.val.obj (op S.val)) :
  tensor_to_unsheafified_homology_component_applied BD M i S m =
  (homotopy_category.homology_functor _ _ _).map
    ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).map
      ((AddCommGroup.adj.hom_equiv _ _).symm (point m))) ≫
      (homology_functor _ _ _).map (eval_freeAb_iso_component _ _ _).inv ≫
    (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
      (op S.val)).homology_functor_iso _ _).inv.app _ :=
begin
  rcases i with ((_|i)|i),
  { refl },
  { apply is_zero.eq_of_src, apply is_zero.homology_is_zero, apply is_zero_zero, },
  { refl },
end



lemma tensor_to_unsheafified_homology_component_applied_of_nat_succ
  (M : Condensed.{u} Ab.{u+1}) (i : ℕ) (S : ExtrDisc.{u}) :
  tensor_to_unsheafified_homology_component_applied BD M (i+1:ℕ) S = 0 :=
begin
  apply is_zero.eq_of_src,
end
-- { apply is_zero.eq_of_src, apply is_zero.homology_is_zero, apply is_zero_zero, }

-/

open category_theory.preadditive

def tensor_to_unsheafified_homology_component (M : Condensed.{u} Ab.{u+1}) (i : ℤ)
  (S : ExtrDisc.{u}) :
  M.val.obj (op S.val) ⟶
  AddCommGroup.of
    (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i ⟶
    (homological_complex.homology ((BD.eval' freeFunc).obj
      (Condensed_Ab_to_presheaf.obj M)) i).obj (op S.val)) :=
add_monoid_hom.mk' (λ m, tensor_to_unsheafified_homology_component_applied _ _ _ _ m)
begin
  intros x y, rcases i with ((_|i)|i),
  { erw [← add_comp, ← functor.map_add, ← functor.map_add], apply congr_arg2 _ _ rfl, congr' 2,
    dsimp only [AddCommGroup.adj, adjunction.mk_of_hom_equiv_hom_equiv],
    ext ⟨⟩, simp only [equiv.symm_symm, add_monoid_hom.add_apply, free_abelian_group.lift.of],
    refl },
  { apply is_zero.eq_of_src,
    apply is_zero.homology_is_zero, apply is_zero_zero },
  { erw [← add_comp, ← functor.map_add, ← functor.map_add], apply congr_arg2 _ _ rfl, congr' 2,
    dsimp only [AddCommGroup.adj, adjunction.mk_of_hom_equiv_hom_equiv],
    ext ⟨⟩, simp only [equiv.symm_symm, add_monoid_hom.add_apply, free_abelian_group.lift.of],
    refl },
end
.

lemma tensor_to_unsheafified_homology_natural (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S T : ExtrDiscᵒᵖ)
  (f : S ⟶ T)
  (x : (((ExtrSheaf_ExtrSheafProd_equiv Ab).functor.obj
             ((Condensed_ExtrSheaf_equiv Ab).inverse.obj M)).val.obj S)) :
  ((tensor_to_unsheafified_homology_component_applied BD M i (unop T)) ((M.val.map f.unop.val.op) x)) =
  ((tensor_to_unsheafified_homology_component_applied BD M i (unop S)) x) ≫
    ((homological_complex.homology ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M)) i).map f.unop.val.op) :=
begin
  dsimp only [tensor_to_unsheafified_homology_component_applied],
  rw [← nat_iso.app_inv, ← category.assoc, iso.comp_inv_eq],
  simp only [category.assoc],
  have := functor.naturality_homology_functor_iso
    ((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).map (ExtrDisc_to_Profinite.op.map f))
    (complex_shape.up ℤ) i,
  apply_fun (λ e, e.app ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))) at this,
  dsimp [-homology_functor_map] at this, simp only [category.id_comp, category.comp_id] at this,
  erw this, rw [← nat_iso.app_inv, ← nat_iso.app_hom, iso.inv_hom_id_assoc],
  clear this,
  rw [← functor.map_iso_inv, ← category.assoc, iso.comp_inv_eq, category.assoc, category.assoc],
  dsimp [-homology_functor_map], simp only [← functor.map_comp],
  rw [← eval_freeAb_iso_component_naturality, iso.inv_hom_id_assoc],
  have :
    ((AddCommGroup.adj.hom_equiv punit (M.val.obj (op (unop T).val))).symm)
    (point ((M.val.map f.unop.val.op) x)) =
    (((AddCommGroup.adj.hom_equiv punit (M.val.obj (op (unop S).val))).symm) (point x)) ≫
    (M.val.map (ExtrDisc_to_Profinite.map f.unop).op),
  { ext ⟨⟩,
    dsimp only [AddCommGroup.adj, adjunction.mk_of_hom_equiv_hom_equiv, equiv.symm,
      equiv.to_fun_as_coe],
    simp only [comp_apply],
    erw free_abelian_group.lift.of,
    erw free_abelian_group.lift.of,
    refl },
  rw [this, functor.map_comp],
  erw [functor.map_comp],
  refl,
end

def tensor_to_unsheafified_homology (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  (((Condensed_ExtrSheaf_equiv Ab).inverse.obj M).tensor
    (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as.homology i)).val ⟶
  ExtrDisc_to_Profinite.op ⋙ homological_complex.homology
    ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M)) i :=
{ app := λ S, AddCommGroup.tensor_uncurry $
    tensor_to_unsheafified_homology_component _ _ _ _,
  naturality' := λ S T f, begin
    apply AddCommGroup.tensor_ext, intros x y,
    dsimp only [ExtrSheaf.tensor, ExtrSheafProd.tensor,
      ExtrSheaf_ExtrSheafProd_equiv, ExtrSheafProd.tensor_presheaf_map,
      AddCommGroup.map_tensor, AddCommGroup.tensor_uncurry],
    erw [comp_apply, comp_apply, tensor_product.map_tmul,
      tensor_product.lift.tmul, tensor_product.lift.tmul],
    dsimp only [add_monoid_hom.coe_to_int_linear_map, linear_map.comp_apply,
      add_monoid_hom.coe_mk, functor.comp_map, Condensed_ExtrSheaf_equiv_inverse_val,
      ExtrDisc_to_Profinite_map, functor.op_map, tensor_to_unsheafified_homology_component,
      add_monoid_hom.mk'_apply],
    erw [id_apply, ← comp_apply], congr' 1,
    apply tensor_to_unsheafified_homology_natural,
  end }

def plain_eval_comparison_component (i : ℤ) (A : AddCommGroup.{u+1}) :
  A ⟶ AddCommGroup.of
  ((homotopy_category.homology_functor _ _ i).obj
    ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj (AddCommGroup.free.obj punit)).val ⟶
    (homotopy_category.homology_functor _ _ i).obj
    ((BD.eval (category_theory.forget AddCommGroup ⋙ AddCommGroup.free)).obj A).val) :=
add_monoid_hom.mk' (λ a, (homotopy_category.homology_functor _ _ _).map $ (BD.eval _).map $
  (AddCommGroup.adj.hom_equiv _ _).symm (point a))
begin
  intros x y, rw [← functor.map_add, ← functor.map_add], congr' 2,
  dsimp only [AddCommGroup.adj, adjunction.mk_of_hom_equiv_hom_equiv],
  ext ⟨⟩, simp only [equiv.symm_symm, add_monoid_hom.add_apply, free_abelian_group.lift.of],
  refl
end

lemma plain_eval_comparison_natural (i : ℤ) (A B : AddCommGroup.{u+1}) (f : A ⟶ B) (x) :
  ((plain_eval_comparison_component BD i B) (f x)) =
  ((plain_eval_comparison_component BD i A) x) ≫
  (homotopy_category.homology_functor AddCommGroup (complex_shape.up ℤ) i).map
    ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).map f) :=
begin
  dsimp only [plain_eval_comparison_component, add_monoid_hom.mk'_apply, functor.comp_map],
  rw [← functor.map_comp], congr' 1,
  erw [← (BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).map_comp], congr' 1,
  dsimp only [AddCommGroup.adj, adjunction.mk_of_hom_equiv_hom_equiv, equiv.symm, equiv.coe_fn_mk,
    equiv.to_fun_as_coe],
  ext ⟨⟩,
  simp only [free_abelian_group.lift.of, comp_apply],
  refl,
end

lemma plain_eval_comparison_natural' (i : ℤ) (A B : AddCommGroup.{u+1}) (f : A ⟶ B) :
  (AddCommGroup.tensor_functor.flip.obj
       (homological_complex.homology
          ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj (AddCommGroup.free.obj punit)) i)).map f ≫
    AddCommGroup.tensor_uncurry (plain_eval_comparison_component BD i B) =
  AddCommGroup.tensor_uncurry (plain_eval_comparison_component BD i A) ≫
    (BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free) ⋙
       homology_functor AddCommGroup (complex_shape.up ℤ) i).map f :=
begin
  apply AddCommGroup.tensor_ext, intros x y,
  rw [comp_apply, comp_apply],
  dsimp only [functor.flip_obj_map, AddCommGroup.tensor_functor_map_app],
  delta AddCommGroup.tensor_uncurry AddCommGroup.map_tensor,
  dsimp only [linear_map.to_add_monoid_hom_coe],
  rw [tensor_product.map_tmul, tensor_product.lift.tmul, tensor_product.lift.tmul],
  dsimp only [add_monoid_hom.coe_to_int_linear_map, linear_map.comp_apply,
    add_monoid_hom.coe_mk],
  rw [plain_eval_comparison_natural],
  refl
end

def plain_eval_comparison (i : ℤ) :
  AddCommGroup.tensor_functor.flip.obj
  (((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).homology i) ⟶
  BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free) ⋙ homology_functor _ _ i :=
{ app := λ A, AddCommGroup.tensor_uncurry $ plain_eval_comparison_component _ _ _,
  naturality' := λ A B f, by apply plain_eval_comparison_natural' }

local attribute [-simp] homology_functor_map

lemma tensor_to_unsheafified_homology_app_eq
  (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S : ExtrDisc.{u}) :
  (tensor_to_unsheafified_homology BD M i).app (op S) =
  (plain_eval_comparison BD i).app (M.val.obj (op S.val)) ≫
  (homology_functor _ _ _).map
  ((eval_freeAb_iso_component _ _ _).inv) ≫
  (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
    (op S.val)).homology_functor_iso _ _).inv.app _  :=
begin
  rw [← nat_iso.app_inv, ← category.assoc, iso.eq_comp_inv, ← functor.map_iso_inv,
    iso.eq_comp_inv, category.assoc, functor.map_iso_hom, nat_iso.app_hom],
  apply_fun AddCommGroup.tensor_curry_equiv _ _ _,
  swap, apply add_equiv.injective,
  dsimp [plain_eval_comparison, tensor_to_unsheafified_homology],
  rw AddCommGroup.tensor_curry_uncurry,
  rw AddCommGroup.tensor_curry_uncurry_comp,
  ext x y,
  dsimp [plain_eval_comparison_component,
    tensor_to_unsheafified_homology_component],
  simp only [comp_apply],
  dsimp [preadditive_yoneda],
  simp only [comp_apply],
  dsimp [tensor_to_unsheafified_homology_component_applied],
  simp only [← comp_apply, category.assoc],
  dsimp only [← nat_iso.app_inv, ← nat_iso.app_hom],
  simp only [iso.inv_hom_id_assoc],
  congr' 2,
  simp only [← category.assoc],
  congr' 1,
  simp only [category.assoc, iso.inv_hom_id, category.comp_id,
    ← functor.map_iso_hom, ← functor.map_iso_inv],
end

def tensor_to_homology_aux (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
((Condensed_ExtrSheaf_equiv Ab).inverse.obj M).tensor
  (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
  (AddCommGroup.free.obj punit)).val.as.homology i) ⟶
  (presheaf_to_Sheaf ExtrDisc.proetale_topology Ab).obj
  (ExtrDisc_to_Profinite.op ⋙
     homological_complex.homology ((BD.eval' freeFunc).obj
     (Condensed_Ab_to_presheaf.obj M)) i) := Sheaf.hom.mk $
tensor_to_unsheafified_homology _ _ _ ≫ grothendieck_topology.to_sheafify _ _

def tensor_to_homology (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  (tensor M $ ((BD.eval $
    category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
    (AddCommGroup.free.obj punit)).val.as.homology i) ⟶
  ((BD.eval freeCond').obj M).val.as.homology i :=
(Condensed_ExtrSheaf_equiv Ab).functor.map
  (tensor_to_homology_aux _ _ _ ≫ ExtrDisc_sheafification_iso.hom.app _)
≫ ((Condensed_ExtrSheaf_equiv _).counit_iso.app _).hom
≫ (homology_functor_sheafification_iso _ _).hom.app _
≫ (homology_functor _ _ _).map (eval_freeCond'_iso_component _ _).inv

.

instance preserves_filtered_colimits_tensor_flip (A) :
  preserves_filtered_colimits (AddCommGroup.tensor_functor.flip.obj A) :=
infer_instance

instance preserves_filtered_colimits_tensor_flip_eval' (i : ℤ) :
  preserves_filtered_colimits
  (AddCommGroup.tensor_functor.flip.obj (homological_complex.homology
    ((BD.eval' (forget AddCommGroup.{u+1} ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)) i)) :=
Condensed.preserves_filtered_colimits_tensor_flip _

set_option pp.universes true

instance additive_tensor_flip (A : AddCommGroup.{u}) : functor.additive
  (AddCommGroup.tensor_functor.flip.obj A) :=
{ map_add' := λ X Y f g, begin
    dsimp [AddCommGroup.map_tensor], ext x,
    dsimp only [linear_map.to_add_monoid_hom_coe, add_monoid_hom.add_apply],
    rw [← linear_map.add_apply],
    congr' 1, apply tensor_product.ext', intros x y,
    apply tensor_product.add_tmul,
  end }

instance additive_tensor_flip_eval' (i : ℤ) : functor.additive
  (AddCommGroup.tensor_functor.flip.obj (homological_complex.homology
    ((BD.eval' (forget AddCommGroup.{u+1} ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)) i)) :=
Condensed.additive_tensor_flip _

-- move me
instance AddCommGroup.free_preserves_limits : preserves_colimits AddCommGroup.free :=
AddCommGroup.adj.left_adjoint_preserves_colimits

instance preserves_filtered_colimits_eval'_forget_free :
  preserves_filtered_colimits.{u+1 u+2 u+2}
    (BD.eval' (forget.{u+2 u+1 u+1} AddCommGroup.{u+1} ⋙ AddCommGroup.free.{u+1})) :=
begin
  apply_with limits.comp_preserves_filtered_colimits.{u+1 u+2 _ u+2} {instances:=ff},
  { apply_with data.eval_functor_preserves_filtered_colimits {instances:=ff},
    apply limits.comp_preserves_filtered_colimits.{u+1 u+2 _ u+2}, },
  { constructor,
    intro J,
    introI,
    introI,
    apply_instance, },
end

instance preserves_filtered_colimits_homology (i : ℤ) :
  preserves_filtered_colimits.{u+1 u+2 u+2}
    (homology_functor.{u+1 u+2 0} AddCommGroup.{u+1} (complex_shape.up.{0} ℤ) i) :=
⟨λ J, begin
  introI,
  introI,
  constructor,
  intro K,
  apply_instance,
end⟩

instance preserves_filtered_colimits_eval'_forget_free_homology (i : ℤ) :
  preserves_filtered_colimits
  (BD.eval' (forget AddCommGroup.{u+1} ⋙ AddCommGroup.free) ⋙
    homology_functor AddCommGroup.{u+1} (complex_shape.up ℤ) i) :=
limits.comp_preserves_filtered_colimits.{u+1 u+2 _ u+2}
  (BD.eval' (forget AddCommGroup.{u+1} ⋙ AddCommGroup.free))
  (homology_functor AddCommGroup.{u+1} (complex_shape.up ℤ) i)

instance _root_.bounded_homotopy_category.forget_additive (𝓐 : Type*) [category 𝓐] [abelian 𝓐] :
  (bounded_homotopy_category.forget 𝓐).additive :=
{ map_add' := λ X Y f g, rfl }

instance additive_eval'_forget_free (i : ℤ) : functor.additive
  (BD.eval' (forget AddCommGroup.{u+1} ⋙ AddCommGroup.free) ⋙
    homology_functor AddCommGroup.{u+1} (complex_shape.up ℤ) i) :=
begin
  show functor.additive (
    (BD.eval (forget AddCommGroup.{u+1} ⋙ AddCommGroup.free) ⋙ bounded_homotopy_category.forget _) ⋙
      homotopy_category.homology_functor _ _ i),
  exact functor.comp.additive (package.eval BD (forget AddCommGroup ⋙ AddCommGroup.free) ⋙ forget AddCommGroup)
  (homotopy_category.homology_functor AddCommGroup (complex_shape.up ℤ) i)
end
.

lemma coeff_star_smul (x : free_abelian_group.{u} punit) :
  free_abelian_group.coeff punit.star x • free_abelian_group.of.{u} punit.star = x :=
begin
  refine free_abelian_group.induction_on'' x _ _ _; clear x,
  { simp only [map_zero, zero_smul], },
  { rintro n hn ⟨⟩, simp only [map_zsmul, free_abelian_group.coeff_of_self, smul_assoc, one_smul], },
  { rintro x n hn ⟨⟩ hx IH1 IH2, simp only [map_add, add_smul, IH1, IH2], },
end

lemma AddCommGroup.adj_hom_equiv_punit (a) :
  ((AddCommGroup.adj.{u+1}.hom_equiv punit.{u+2}
    (AddCommGroup.free.{u+1}.obj punit.{u+2})).symm) (point.{u+1} a) =
    (free_abelian_group.coeff punit.star a) • 𝟙 _ :=
begin
  dsimp only [AddCommGroup.adj, adjunction.mk_of_hom_equiv_hom_equiv, equiv.symm, equiv.coe_fn_mk, equiv.to_fun_as_coe],
  ext ⟨⟩,
  rw [free_abelian_group.lift.of, add_monoid_hom.smul_apply, id_apply, coeff_star_smul],
  refl
end

lemma homology_functor.map_id_bo_ho_ca {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  (X : bounded_homotopy_category 𝓐) (i : ℤ) :
  (homotopy_category.homology_functor _ (complex_shape.up ℤ) i).map (𝟙 X : _) =
    𝟙 ((homotopy_category.homology_functor _ (complex_shape.up ℤ) i).obj X.val) :=
category_theory.functor.map_id _ _

lemma plain_eval_comparison_is_iso_aux (A : AddCommGroup) :
  is_iso (AddCommGroup.tensor_uncurry $ add_monoid_hom.mk' (λ (a : (AddCommGroup.free.obj punit)),
     (free_abelian_group.coeff punit.star) a • 𝟙 A) $ by intros; simp only [map_add, add_smul]) :=
begin
  constructor,
  refine ⟨add_monoid_hom.mk' (λ a, free_abelian_group.of punit.star ⊗ₜ a) _, _, _⟩,
  { intros, rw tensor_product.tmul_add, },
  { apply AddCommGroup.tensor_ext, intros x y,
    erw [comp_apply, id_apply],
    dsimp only [AddCommGroup.tensor_uncurry, add_monoid_hom.mk'_apply,
      linear_map.to_add_monoid_hom_coe],
    rw [tensor_product.lift.tmul],
    dsimp only [add_monoid_hom.coe_to_int_linear_map, linear_map.comp_apply,
      add_monoid_hom.coe_mk, add_monoid_hom.mk'_apply, add_monoid_hom.smul_apply],
    rw [← tensor_product.smul_tmul, id_apply, coeff_star_smul], },
  { ext a, rw [id_apply, comp_apply],
    dsimp only [AddCommGroup.tensor_uncurry, add_monoid_hom.mk'_apply,
      linear_map.to_add_monoid_hom_coe],
    rw [tensor_product.lift.tmul],
    dsimp only [add_monoid_hom.coe_to_int_linear_map, linear_map.comp_apply,
      add_monoid_hom.coe_mk, add_monoid_hom.mk'_apply, add_monoid_hom.smul_apply],
    rw [free_abelian_group.coeff_of_self, one_smul], refl }
end

instance (i : ℤ) : is_iso ((plain_eval_comparison BD i).app
  (AddCommGroup.free.obj (punit : Type (u+1)))) :=
begin
  dsimp only [plain_eval_comparison, plain_eval_comparison_component],
  simp only [AddCommGroup.adj_hom_equiv_punit, functor.map_smul,
    category_theory.functor.map_id, homology_functor.map_id_bo_ho_ca],
  apply plain_eval_comparison_is_iso_aux
end

lemma AddCommGroup.free_punit_is_tensor_unit :
  (AddCommGroup.free.{u+1}.obj punit.{u+2}).is_tensor_unit :=
begin
  constructor, intros B, swap, exact free_abelian_group.of punit.star,
  split, { intros f g h, ext ⟨⟩, exact h },
  intros b, refine ⟨free_abelian_group.lift (point b), _⟩,
  dsimp only, rw [free_abelian_group.lift.of], refl,
end

instance is_iso_map_tensor_to_homology_aux_comp (M : Condensed.{u} Ab.{u+1}) (i : ℤ)
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (M.val.obj (op S.val))] :
  is_iso (tensor_to_homology_aux BD M i) :=
begin
  suffices : ∀ (X : ExtrDisc), is_iso ((tensor_to_unsheafified_homology BD M i).app (op X)),
  { resetI,
    apply Sheaf.is_iso_of_eval _ (tensor_to_homology_aux BD M i)
      (tensor_to_unsheafified_homology _ _ _) rfl },
  intros S,
  rw tensor_to_unsheafified_homology_app_eq,
  suffices : is_iso ((plain_eval_comparison BD i).app (M.val.obj (op S.val))),
  { resetI, apply is_iso.comp_is_iso },
  apply AddCommGroup.is_iso_of_preserves_of_is_tensor_unit.{u+1 u+2} _ _
    (plain_eval_comparison BD i) (AddCommGroup.free.obj punit),
  apply AddCommGroup.free_punit_is_tensor_unit,
end

instance is_iso_tensor_to_homology (M : Condensed.{u} Ab.{u+1}) (i : ℤ)
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (M.val.obj (op S.val))] :
  is_iso (tensor_to_homology BD M i) :=
begin
  dsimp only [tensor_to_homology],
  apply is_iso.comp_is_iso,
end

def homology_bd_eval (M : Condensed.{u} Ab.{u+1})
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (M.val.obj (op S.val))] (i : ℤ) :
  ((BD.eval freeCond').obj M).val.as.homology i ≅
  (tensor M $ ((BD.eval $
    category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
      (AddCommGroup.free.obj punit)).val.as.homology i) :=
(as_iso (tensor_to_homology BD M i)).symm

section
variables (M N : Condensed.{u} Ab.{u+1}) (f : M ⟶ N)

set_option pp.universes false

@[simp] lemma embed_f_0 {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  {X Y : chain_complex 𝓐 ℕ} (f : X ⟶ Y) :
  ((homological_complex.embed complex_shape.embedding.nat_down_int_up).map f).f 0 = f.f 0 := rfl

@[simp] lemma embed_f_neg {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  {X Y : chain_complex 𝓐 ℕ} (f : X ⟶ Y) (n : ℕ) :
  ((homological_complex.embed complex_shape.embedding.nat_down_int_up).map f).f -[1+ n] = f.f (n+1) := rfl

lemma eval_freeCond'_iso_component_zero_natural :
  (eval_freeCond'_iso.component_zero BD M).inv ≫ ((BD.eval' freeCond').map f).f 0 =
  ((presheaf_to_Condensed_Ab.map_homological_complex (complex_shape.up ℤ)).map
    ((BD.eval' freeFunc).map (Condensed_Ab_to_presheaf.map f))).f 0 ≫
      (eval_freeCond'_iso.component_zero BD N).inv :=
begin
  dsimp only [eval_freeCond'_iso.component_zero, package.eval',
    functor.map_iso_trans, iso.trans_inv, functor.map_iso_inv,
    iso_whisker_right_inv,
    functor.map_homological_complex_map_f, functor.comp_map,
    functor.comp_obj, functor.flip_obj_map, homological_complex.functor_eval,
    embed_f_0, data.eval_functor, data.eval_functor'_obj_X_map],
  simp only [functor.map_biproduct, category.assoc],
  simp only [biproduct.unique_up_to_iso_inv, functor.map_comp,
    Condensed_Ab_to_CondensedSet_map, CondensedSet_to_Condensed_Ab_map,
    whisker_right_twice, category.assoc, whiskering_right_obj_map],
  dsimp only [presheaf_to_Condensed_Ab],
  simp only [← functor.map_comp], congr' 1,
  ext t : 2, dsimp only [nat_trans.comp_app, whisker_right_app, functor.associator],
  simp only [category.id_comp, category.comp_id],
  simp only [← functor.map_comp], congr' 1,
  simp only [← nat_trans.comp_app], congr' 1,
  apply biproduct.hom_ext', intros j,
  simp only [category.assoc, biproduct.ι_desc_assoc, biproduct.ι_desc,
    biproduct.ι_map_assoc],
  dsimp only [functor.map_bicone, Condensed_Ab_to_presheaf, ← Sheaf_to_presheaf_map],
  simp only [← functor.map_comp], congr' 1,
  erw biproduct.ι_map,
end

lemma eval_freeCond'_iso_component_neg_natural (n : ℕ) :
  (eval_freeCond'_iso.component_neg BD M n).inv ≫ ((BD.eval' freeCond').map f).f (-[1+ n]) =
  ((presheaf_to_Condensed_Ab.map_homological_complex (complex_shape.up ℤ)).map
    ((BD.eval' freeFunc).map (Condensed_Ab_to_presheaf.map f))).f -[1+ n] ≫
      (eval_freeCond'_iso.component_neg BD N n).inv :=
begin
  dsimp only [eval_freeCond'_iso.component_neg, package.eval',
    functor.map_iso_trans, iso.trans_inv, functor.map_iso_inv,
    iso_whisker_right_inv,
    functor.map_homological_complex_map_f, functor.comp_map,
    functor.comp_obj, functor.flip_obj_map, homological_complex.functor_eval,
    embed_f_neg, data.eval_functor, data.eval_functor'_obj_X_map],
  simp only [functor.map_biproduct, category.assoc],
  simp only [biproduct.unique_up_to_iso_inv, functor.map_comp,
    Condensed_Ab_to_CondensedSet_map, CondensedSet_to_Condensed_Ab_map,
    whisker_right_twice, category.assoc, whiskering_right_obj_map],
  dsimp only [presheaf_to_Condensed_Ab],
  simp only [← functor.map_comp], congr' 1,
  ext t : 2, dsimp only [nat_trans.comp_app, whisker_right_app, functor.associator],
  simp only [category.id_comp, category.comp_id],
  simp only [← functor.map_comp], congr' 1,
  simp only [← nat_trans.comp_app], congr' 1,
  apply biproduct.hom_ext', intros j,
  simp only [category.assoc, biproduct.ι_desc_assoc, biproduct.ι_desc,
    biproduct.ι_map_assoc],
  dsimp only [functor.map_bicone, Condensed_Ab_to_presheaf, ← Sheaf_to_presheaf_map],
  simp only [← functor.map_comp], congr' 1,
  erw biproduct.ι_map,
end

lemma eval_freeCond'_iso_component_natural :
  (eval_freeCond'_iso_component.{u} BD M).inv ≫ (BD.eval' freeCond'.{u}).map f =
  (presheaf_to_Condensed_Ab.{u}.map_homological_complex (complex_shape.up.{0} ℤ)).map
    ((BD.eval' freeFunc.{u u+1}).map (Condensed_Ab_to_presheaf.{u}.map f)) ≫
      (eval_freeCond'_iso_component.{u} BD N).inv :=
begin
  ext ((_|n)|n) : 2,
  { apply eval_freeCond'_iso_component_zero_natural },
  { apply is_zero.eq_of_tgt, exact is_zero_zero _, },
  { apply eval_freeCond'_iso_component_neg_natural },
end

lemma tensor_to_homology_natural
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (M.val.obj (op S.val))]
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (N.val.obj (op S.val))] (i : ℤ) :
  tensor_to_homology.{u} BD M i ≫ (homology_functor (Condensed.{u} Ab.{u+1}) _ i).map
      ((BD.eval' freeCond').map f) =
  map_tensor f (𝟙 _) ≫ tensor_to_homology.{u} BD N i :=
begin
  simp only [tensor_to_homology, category.assoc, ← functor.map_comp,
    eval_freeCond'_iso_component_natural],
  simp only [functor.map_comp],
  simp only [← category.assoc], refine congr_arg2 _ _ rfl, simp only [category.assoc],
  have := (homology_functor_sheafification_iso (complex_shape.up ℤ) i).hom.naturality
    ((Condensed_Ab_to_presheaf ⋙ BD.eval' freeFunc).map f),
  erw [← this], clear this,
  simp only [← category.assoc], refine congr_arg2 _ _ rfl, simp only [category.assoc],
  dsimp only [iso.app_hom],
  have := (Condensed_ExtrSheaf_equiv Ab.{u+1}).counit_iso.hom.naturality
    ((homology_functor (Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) _ i ⋙
      presheaf_to_Condensed_Ab).map ((Condensed_Ab_to_presheaf ⋙ BD.eval' freeFunc.{u u+1}).map f)),
  erw [← this], clear this,
  simp only [← category.assoc], refine congr_arg2 _ _ rfl, simp only [category.assoc],
  dsimp only [map_tensor, functor.comp_map],
  simp only [← functor.map_comp], congr' 1,
  have := ExtrDisc_sheafification_iso.hom.naturality
    ((homology_functor (Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) _ i).map
      ((BD.eval' freeFunc).map (Condensed_Ab_to_presheaf.map f))),
  erw [← this], clear this,
  simp only [← category.assoc], refine congr_arg2 _ _ rfl,
  -- jmc is not sure that the following steps are good moves
  ext S : 3,
  dsimp only [functor.comp_map, whiskering_left_obj_map, tensor_to_homology_aux,
    Sheaf.hom.comp_val, nat_trans.comp_app],
  simp only [category.assoc],
  -- erw [← nat_trans.naturality],
  --  nat_trans.naturality_assoc],
  sorry
end

lemma homology_bd_eval_natural
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (M.val.obj (op S.val))]
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (N.val.obj (op S.val))] (i : ℤ) :
  (homology_bd_eval BD M i).inv ≫ (homology_functor _ _ i).map ((BD.eval' freeCond').map f) =
  map_tensor f (𝟙 _) ≫ (homology_bd_eval BD N i).inv :=
tensor_to_homology_natural BD M N f i

end

end Condensed
