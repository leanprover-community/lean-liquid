import breen_deligne.main
import breen_deligne.eg
import condensed.tensor
import condensed.evaluation_homology
import condensed.sheafification_homology
import pseudo_normed_group.QprimeFP
import for_mathlib.AddCommGroup
import for_mathlib.map_to_sheaf_is_iso
import condensed.is_iso_iff_extrdisc
import Lbar.torsion_free_condensed
import condensed.ab5
import condensed.ab4
import for_mathlib.endomorphisms.ab4

.

noncomputable theory

universes u

open category_theory category_theory.limits breen_deligne opposite
open bounded_homotopy_category

namespace Condensed

variables (BD : package)

abbreviation freeFunc : (Profiniteᵒᵖ ⥤ Ab) ⥤ Profiniteᵒᵖ ⥤ Ab :=
(whiskering_right _ _ _).obj (forget _ ⋙ AddCommGroup.free)

def eval_freeCond'_iso_component (M : Condensed.{u} Ab.{u+1}) :
  ((BD.eval' freeCond').obj M) ≅
  (presheaf_to_Condensed_Ab.map_homological_complex _).obj
  ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M)) :=
homological_complex.hom.iso_of_components
(λ i,
match i with
| int.of_nat 0 := presheaf_to_Condensed_Ab.map_iso begin
    refine functor.associator _ _ _ ≪≫ _,
    refine iso_whisker_right _ _,
    refine (Condensed_Ab_to_presheaf.map_biproduct _),
  end
| int.of_nat (i+1) := is_zero.iso (is_zero_zero _) (functor.map_is_zero _ $ is_zero_zero _)
| -[1+i] := presheaf_to_Condensed_Ab.map_iso begin
    refine functor.associator _ _ _ ≪≫ _,
    refine iso_whisker_right _ _,
    refine (Condensed_Ab_to_presheaf.map_biproduct _)
  end
end )
sorry
.

def eval_freeAb_iso_component (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) :
  (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op S.val)).map_homological_complex
    (complex_shape.up ℤ)).obj
  ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M)) ≅
  (BD.eval' $ category_theory.forget _ ⋙ AddCommGroup.free).obj (M.val.obj (op S.val)) :=
homological_complex.hom.iso_of_components
(λ i,
match i with
| int.of_nat 0 := begin
    refine AddCommGroup.free.map_iso _,
    refine (category_theory.forget _).map_iso _,
    refine ((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op S.val)).map_biproduct _
  end
| int.of_nat (i+1) := is_zero.iso (functor.map_is_zero _ $ is_zero_zero _) (is_zero_zero _)
| -[1+i] := begin
    refine AddCommGroup.free.map_iso _,
    refine (category_theory.forget _).map_iso _,
    refine ((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op S.val)).map_biproduct _
  end
end )
begin
  rintro i _ (rfl : _=_),
  sorry
end
.

def eval_freeCond'_iso :
  BD.eval' freeCond' ≅
  Condensed_Ab_to_presheaf ⋙ BD.eval' freeFunc ⋙ presheaf_to_Condensed_Ab.map_homological_complex _ :=
nat_iso.of_components
(λ M, eval_freeCond'_iso_component _ _)
begin
  intros X Y f,
  ext ((_|i)|i) : 2,
  { sorry },
  { apply is_zero.eq_of_src, apply is_zero_zero },
  { sorry }
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
  { sorry },
  { apply is_zero.eq_of_tgt, apply is_zero_zero },
  { sorry }
end

-- Move this.
def point {A : Type u} (a : A) : punit.{u+1} ⟶ A := λ _, a

def tensor_to_unsheafified_homology_component_applied
  (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S : ExtrDisc.{u}) (m : M.val.obj (op S.val)) :
  ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as.homology i ⟶
  (homological_complex.homology ((BD.eval' freeFunc).obj
    (Condensed_Ab_to_presheaf.obj M)) i).obj (op S.val) :=
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

lemma tensor_to_unsheafified_homology_component_applied_of_nat_succ
  (M : Condensed.{u} Ab.{u+1}) (i : ℕ) (S : ExtrDisc.{u}) :
  tensor_to_unsheafified_homology_component_applied BD M (i+1:ℕ) S = 0 := rfl

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
  { symmetry, apply add_zero, },
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
  rcases i with ((_|i)|i),
  { erw [category.assoc, category.assoc],
    sorry },
  { erw [tensor_to_unsheafified_homology_component_applied_of_nat_succ,
        tensor_to_unsheafified_homology_component_applied_of_nat_succ, zero_comp], refl, },
  { sorry },
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

lemma tensor_to_unsheafified_homology_app_eq
  (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S : ExtrDisc.{u}) :
  (tensor_to_unsheafified_homology BD M i).app (op S) =
  (plain_eval_comparison BD i).app (M.val.obj (op S.val)) ≫
  (homology_functor _ _ _).map
  ((eval_freeAb_iso_component _ _ _).inv) ≫
  (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
    (op S.val)).homology_functor_iso _ _).inv.app _  := sorry --- possibly challenging

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
  { sorry }
end

instance preserves_filtered_colimits_homology (i : ℤ) :
  preserves_filtered_colimits.{u+1 u+2 u+2}
    (homology_functor.{u+1 u+2 0} AddCommGroup.{u+1} (complex_shape.up.{0} ℤ) i) :=
sorry

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
  sorry { apply AddCommGroup.tensor_ext, intros x y,
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
  sorry
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

def eval_freeCond_homology_zero :
  ((data.eval_functor freeCond').obj breen_deligne.eg.data) ⋙ homology_functor _ _ 0 ≅ 𝟭 _ :=
sorry

instance (α : Type (u+1)) (M) :
  preserves_colimits_of_shape (discrete α) (endo_tensor.obj M) :=
sorry

lemma bd_lemma (A : Condensed.{u} Ab.{u+1}) (B : Condensed.{u} Ab.{u+1})
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (A.val.obj (op S.val))]
  (f : A ⟶ A) (g : B ⟶ B) :
  (∀ i, is_iso $ ((Ext' i).map f.op).app B - ((Ext' i).obj (op A)).map g) ↔
  (∀ i, is_iso $
    ((Ext i).map ((breen_deligne.eg.eval freeCond').map f).op).app ((single _ 0).obj B) -
    ((Ext i).obj (op $ (breen_deligne.eg.eval freeCond').obj A)).map ((single _ 0).map g)) :=
begin
  refine package.main_lemma _ _ _ _ _ _ eval_freeCond_homology_zero (endo_tensor.obj ⟨A,f⟩) _ _ _,
  { sorry },
  { sorry },
  { sorry }
end

end Condensed
