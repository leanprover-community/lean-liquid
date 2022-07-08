import condensed.Qprime_isoms

.

noncomputable theory

universes v u

open category_theory category_theory.limits breen_deligne opposite
open bounded_homotopy_category

namespace Condensed

variables (BD : package)
variables (M N : Condensed.{u} Ab.{u+1}) (f : M ⟶ N)

section
variables {X A B : Type*} [category X] [category.{v} A] [category.{v} B] [abelian A] [abelian B]
variables {ι : Type*} {c : complex_shape ι} (i : ι)
variables (𝓕₁ 𝓕₂ : X ⥤ A) (φ : 𝓕₁ ⟶ 𝓕₂) (G : (X ⥤ A) ⥤ homological_complex (X ⥤ A) c) (S : X)
-- variables (F : A ⥤ B) [functor.additive F] [preserves_finite_limits F] [preserves_finite_colimits F]

-- lemma homology_functor_iso_natural :
--   (((category_theory.evaluation X A).obj S).homology_functor_iso c i).inv.app (G.obj M) ≫
--     ((homology_functor (X ⥤ Ab) c i).map (G.map f)).app S =
--     _ := sorry

end

lemma tensor_to_unsheafified_homology_natural'
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (M.val.obj (op S.val))]
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (N.val.obj (op S.val))] (i : ℤ) :
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
  sorry
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
