import condensed.Qprime_isoms

.

noncomputable theory

universes v u u₁ u₂

open category_theory category_theory.limits breen_deligne opposite
open bounded_homotopy_category

namespace Condensed

variables (BD : package)
variables (M N : Condensed.{u} Ab.{u+1}) (f : M ⟶ N)

lemma homology_functor_iso_natural'
  (C₁ C₂ : cochain_complex (Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) ℤ) (g : C₁ ⟶ C₂)
  (S : Profinite.{u}ᵒᵖ) (i : ℤ) :
  (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj S).homology_functor_iso (complex_shape.up ℤ) i).inv.app C₁ ≫
  ((homology_functor (Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) (complex_shape.up ℤ) i).map g).app S =
  category_theory.functor.map _ g ≫
      (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj S).homology_functor_iso (complex_shape.up ℤ) i).inv.app C₂ :=
((((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj S).homology_functor_iso _ i).inv.naturality g).symm

lemma homology_functor_iso_natural (S : ExtrDiscᵒᵖ) (i : ℤ) :
  (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
      (op (unop S).val)).homology_functor_iso (complex_shape.up ℤ) i).inv.app
    ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M)) ≫
  ((homology_functor (Profiniteᵒᵖ ⥤ Ab) (complex_shape.up ℤ) i).map
     ((BD.eval' freeFunc).map (Condensed_Ab_to_presheaf.map f))).app
    (ExtrDisc_to_Profinite.op.obj S) =
  category_theory.functor.map _ (category_theory.functor.map _ (category_theory.functor.map _ f)) ≫
      (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
        (op (unop S).val)).homology_functor_iso (complex_shape.up ℤ) i).inv.app
      ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj N)) :=
homology_functor_iso_natural' _ _ _ _ _
.

lemma eval_freeAb_iso_component_natural_zero (S : ExtrDiscᵒᵖ) :
  ((((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op (unop S).val)).map_homological_complex
        (complex_shape.up ℤ)).map
       ((BD.eval' freeFunc).map (Condensed_Ab_to_presheaf.map f))).f
      (int.of_nat 0) ≫
    (eval_freeAb_iso.component_zero BD N (unop S)).hom =
  (eval_freeAb_iso.component_zero BD M (unop S)).hom ≫
    ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).map
       (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op (unop S).val)).map f.val)).f
      (int.of_nat 0) :=
begin
  dsimp only [eval_freeAb_iso.component_zero,
    functor.map_homological_complex_map_f, category_theory.evaluation_obj_map],
  erw [embed_f_0, embed_f_0],
  simp only [functor.map_biproduct, data.eval_functor_obj_map_f,
    whiskering_right_obj_map, whisker_right_app, functor.comp_map,
    functor.map_iso_hom, biproduct.unique_up_to_iso_hom,
    ← functor.map_comp], congr' 2,
  apply biproduct.hom_ext, intro j,
  simp only [category.assoc],
  erw [biproduct.lift_π, biproduct.map_π, biproduct.lift_π_assoc],
  simp only [functor.map_bicone_π, biproduct.bicone_π, evaluation_obj_map],
  simp only [← nat_trans.comp_app], congr' 1,
  rw [biproduct.map_π], refl,
end

lemma eval_freeAb_iso_component_natural_neg (S : ExtrDiscᵒᵖ) (n : ℕ) :
((((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op (unop S).val)).map_homological_complex
        (complex_shape.up ℤ)).map
       ((BD.eval' freeFunc).map (Condensed_Ab_to_presheaf.map f))).f
      -[1+ n] ≫
    (eval_freeAb_iso.component_neg BD N (unop S) n).hom =
  (eval_freeAb_iso.component_neg BD M (unop S) n).hom ≫
    ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).map
       (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op (unop S).val)).map f.val)).f
      -[1+ n] :=
begin
  dsimp only [eval_freeAb_iso.component_neg,
    functor.map_homological_complex_map_f, category_theory.evaluation_obj_map],
  erw [embed_f_neg, embed_f_neg],
  simp only [functor.map_biproduct, data.eval_functor_obj_map_f,
    whiskering_right_obj_map, whisker_right_app, functor.comp_map,
    functor.map_iso_hom, biproduct.unique_up_to_iso_hom,
    ← functor.map_comp], congr' 2,
  apply biproduct.hom_ext, intro j,
  simp only [category.assoc],
  erw [biproduct.lift_π, biproduct.map_π, biproduct.lift_π_assoc],
  simp only [functor.map_bicone_π, biproduct.bicone_π, evaluation_obj_map],
  simp only [← nat_trans.comp_app], congr' 1,
  rw [biproduct.map_π], refl,
end

lemma eval_freeAb_iso_component_natural (S : ExtrDiscᵒᵖ) :
(eval_freeAb_iso_component BD M (unop S)).inv ≫
    (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op (unop S).val)).map_homological_complex
       (complex_shape.up ℤ)).map
      ((BD.eval' freeFunc).map (Condensed_Ab_to_presheaf.map f)) =
  (BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).map
      (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op (unop S).val)).map f.val) ≫
    (eval_freeAb_iso_component BD N (unop S)).inv :=
begin
  rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv],
  ext ((_|n)|n) : 2,
  { apply eval_freeAb_iso_component_natural_zero },
  { apply is_zero.eq_of_tgt, apply is_zero_zero, },
  { apply eval_freeAb_iso_component_natural_neg },
end
.

lemma eval_freeAb_iso_component_natural_bis (S : ExtrDiscᵒᵖ) (i : ℤ) :
  (homology_functor AddCommGroup (complex_shape.up ℤ) i).map (eval_freeAb_iso_component BD M (unop S)).inv ≫
  (((category_theory.evaluation Profiniteᵒᵖ Ab).obj (op (unop S).val)).map_homological_complex
       (complex_shape.up ℤ) ⋙
     homology_functor Ab (complex_shape.up ℤ) i).map
    ((BD.eval' freeFunc).map (Condensed_Ab_to_presheaf.map f)) =
  category_theory.functor.map _ (category_theory.functor.map _ (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
      (op (unop S).val)).map f.val)) ≫
    (homology_functor AddCommGroup (complex_shape.up ℤ) i).map (eval_freeAb_iso_component BD N (unop S)).inv :=
begin
  rw [functor.comp_map, ← functor.map_comp, ← functor.map_comp], congr' 1,
  apply eval_freeAb_iso_component_natural,
end

lemma tensor_to_unsheafified_homology_natural'_aux (S : ExtrDiscᵒᵖ) (x) :
  ((AddCommGroup.adj.hom_equiv punit (N.val.obj (op (unop S).val))).symm)
  (point
     ((((ExtrSheaf_ExtrSheafProd_equiv Ab).functor.map ((Condensed_ExtrSheaf_equiv Ab).inverse.map f)).val.app S) x)) =
  ((AddCommGroup.adj.hom_equiv punit (M.val.obj (op (unop S).val))).symm) (point x) ≫
    ((category_theory.evaluation Profiniteᵒᵖ Ab).obj (op (unop S).val)).map f.val :=
begin
  dsimp [AddCommGroup.adj, adjunction.mk_of_hom_equiv_hom_equiv],
  apply free_abelian_group.lift.ext, rintro ⟨⟩,
  rw [free_abelian_group.lift.of, comp_apply, free_abelian_group.lift.of],
  refl
end

lemma aaaahrg (i : ℤ) {A B : Ab} (f : A ⟶ B) :
  (homotopy_category.homology_functor AddCommGroup (complex_shape.up ℤ) i).map
  ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).map f) =
  (homology_functor AddCommGroup (complex_shape.up ℤ) i).map
  ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).map f) :=
rfl

lemma tensor_to_unsheafified_homology_natural' (i : ℤ) :
  tensor_to_unsheafified_homology BD M i ≫
    whisker_left ExtrDisc_to_Profinite.op
      ((homology_functor (Profiniteᵒᵖ ⥤ Ab) (complex_shape.up ℤ) i).map
         ((BD.eval' freeFunc).map (Condensed_Ab_to_presheaf.map f))) =
  (ExtrSheafProd.map_tensor
    ((ExtrSheaf_ExtrSheafProd_equiv Ab).functor.map ((Condensed_ExtrSheaf_equiv Ab).inverse.map f))
      (𝟙 (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj (AddCommGroup.free.obj punit)).val.as.homology i))).val ≫
    tensor_to_unsheafified_homology BD N i :=
begin
  ext S : 2,
  dsimp only [tensor_to_unsheafified_homology, nat_trans.comp_app, whisker_left_app,
    ExtrSheafProd.map_tensor_val_app],
  apply AddCommGroup.tensor_ext, intros x y,
  simp only [comp_apply, id_apply, AddCommGroup.map_tensor, tensor_product.map_tmul,
    AddCommGroup.tensor_uncurry, linear_map.to_add_monoid_hom_coe,
    tensor_product.lift.tmul, add_monoid_hom.coe_mk,
    linear_map.comp_apply, add_monoid_hom.coe_to_int_linear_map],
  dsimp only [tensor_to_unsheafified_homology_component, add_monoid_hom.mk'_apply,
    tensor_to_unsheafified_homology_component_applied],
  simp only [← comp_apply, category.assoc], congr' 1,
  rw homology_functor_iso_natural,
  simp only [← category.assoc], congr' 1, simp only [category.assoc],
  rw eval_freeAb_iso_component_natural_bis,
  simp only [← category.assoc], congr' 1,
  rw [tensor_to_unsheafified_homology_natural'_aux],
  rw [aaaahrg, aaaahrg, ← category_theory.functor.map_comp, ← category_theory.functor.map_comp],
end

lemma tensor_to_homology_natural (i : ℤ) :
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
  ext1,
  dsimp only [tensor_to_homology_aux],
  simp only [functor.comp_map, whiskering_left_obj_map, Sheaf.category_theory.category_comp_val,
    presheaf_to_Sheaf_map_val, ExtrSheaf.map_tensor_val,
    grothendieck_topology.to_sheafify_naturality, category.assoc,
    grothendieck_topology.to_sheafify_naturality_assoc, ← grothendieck_topology.sheafify_map_comp],
  rw [tensor_to_unsheafified_homology_natural'],
end

lemma homology_bd_eval_natural
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (M.val.obj (op S.val))]
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (N.val.obj (op S.val))] (i : ℤ) :
  (homology_bd_eval BD M i).inv ≫ (homology_functor _ _ i).map ((BD.eval' freeCond').map f) =
  map_tensor f (𝟙 _) ≫ (homology_bd_eval BD N i).inv :=
tensor_to_homology_natural BD M N f i

end Condensed
