import breen_deligne.main
import breen_deligne.eg
import condensed.tensor
import condensed.evaluation_homology
import condensed.sheafification_homology
import pseudo_normed_group.QprimeFP
import for_mathlib.AddCommGroup
import condensed.is_iso_iff_extrdisc

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
| int.of_nat (i+1) := is_zero.iso (is_zero_zero _) sorry
| -[1+i] := presheaf_to_Condensed_Ab.map_iso begin
    refine functor.associator _ _ _ ≪≫ _,
    refine iso_whisker_right _ _,
    refine (Condensed_Ab_to_presheaf.map_biproduct _)
  end
end )
sorry

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
| int.of_nat (i+1) := is_zero.iso sorry (is_zero_zero _)
| -[1+i] := begin
    refine AddCommGroup.free.map_iso _,
    refine (category_theory.forget _).map_iso _,
    refine ((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj (op S.val)).map_biproduct _
  end
end )
sorry

def eval_freeCond'_iso :
  BD.eval' freeCond' ≅
  Condensed_Ab_to_presheaf ⋙
  BD.eval' freeFunc ⋙
  presheaf_to_Condensed_Ab.map_homological_complex _ :=
nat_iso.of_components
(λ M, eval_freeCond'_iso_component _ _)
sorry

def eval_freeAb_iso (S : ExtrDisc.{u}) :
  Condensed_Ab_to_presheaf ⋙ BD.eval' freeFunc ⋙
  ((category_theory.evaluation _ _).obj (op S.val)).map_homological_complex _ ≅
  evaluation _ S.val ⋙ BD.eval' (category_theory.forget _ ⋙ AddCommGroup.free) :=
nat_iso.of_components
(λ M, eval_freeAb_iso_component _ _ _)
sorry

/-
def eval_comparison (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) (m : M.val.obj (op S.val)) :
  ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)) ⟶
  ((evaluation AddCommGroup S.val).map_homological_complex (complex_shape.up ℤ)).obj
    ((presheaf_to_Condensed_Ab.map_homological_complex (complex_shape.up ℤ)).obj
       ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))) :=
{ f := λ i,
  match i with
  | int.of_nat 0 := begin
      refine _ ≫ (proetale_topology.to_sheafify _).app _,
      refine AddCommGroup.free.map _,
      refine (category_theory.forget AddCommGroup).map _,
      refine _ ≫ (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
        (op S.val)).map_biproduct
        (λ (i : ulift (fin (BD.data.X 0))), Condensed_Ab_to_presheaf.obj M)).inv,
      refine limits.biproduct.map (λ j : ulift (fin (BD.data.X 0)), _),
      refine (AddCommGroup.adj.hom_equiv _ _).symm _,
      exact (λ _, m), -- maybe change this to `types.pt` or something...
    end
  | int.of_nat (i+1) := 0
  | -[1+i] := begin
      refine _ ≫ (proetale_topology.to_sheafify _).app _,
      refine AddCommGroup.free.map _,
      refine (category_theory.forget AddCommGroup).map _,
      refine _ ≫ (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
        (op S.val)).map_biproduct
        (λ (i : ulift (fin (BD.data.X _))), Condensed_Ab_to_presheaf.obj M)).inv,
      refine limits.biproduct.map (λ j : ulift (fin (BD.data.X _)), _),
      refine (AddCommGroup.adj.hom_equiv _ _).symm _,
      exact (λ _, m),
    end
  end,
  comm' := sorry }

def plain_eval_comparison (i : ℤ) :
  AddCommGroup.tensor_functor.flip.obj
  (((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).homology i) ⟶
  BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free) ⋙ homology_functor _ _ i :=
sorry
-/

def uncurried_tensor_to_homology_component (M : Condensed.{u} Ab.{u+1}) (i : ℤ)
  (S : ExtrDisc.{u}) :
  M.val.obj (op S.val) ⟶
  AddCommGroup.of
    (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i ⟶
     (presheaf_to_Condensed_Ab.obj
        (homological_complex.homology
        ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M)) i)).val.obj (op S.val)) :=
{ to_fun := λ m, begin
    refine _ ≫ (proetale_topology.to_sheafify _).app _,
    refine _ ≫
      (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
      (op S.val)).homology_functor_iso _ _).inv.app _,
    refine (homology_functor _ _ _).map _,
    refine _ ≫ (eval_freeAb_iso_component _ _ _).inv,
    refine (BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).map _,
    refine (AddCommGroup.adj.hom_equiv _ _).symm _,
    exact (λ _, m),
  end,
  map_zero' := sorry,
  map_add' := sorry }

def uncurried_tensor_to_homology (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  (Condensed_ExtrSheafProd_equiv Ab).functor.obj M ⟶
  ExtrSheafProd.half_internal_hom
    (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i)
    ((Condensed_ExtrSheafProd_equiv Ab).functor.obj
       (presheaf_to_Condensed_Ab.obj
          ((homology_functor (Profiniteᵒᵖ ⥤ Ab) (complex_shape.up ℤ) i).obj
             ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M))))) :=
ExtrSheafProd.hom.mk $
{ app := λ S, uncurried_tensor_to_homology_component _ _ _ _,
  naturality' := sorry }

def tensor_to_homology (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  M.tensor (((BD.eval $
    category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
      (AddCommGroup.free.obj punit)).val.as.homology i) ⟶
  ((BD.eval freeCond').obj M).val.as.homology i :=
(Condensed_ExtrSheafProd_equiv _).inverse.map
(ExtrSheafProd.tensor_uncurry (uncurried_tensor_to_homology _ _ _)) ≫
(Condensed_ExtrSheafProd_equiv _).unit_iso.inv.app _ ≫
(homology_functor_sheafification_iso (complex_shape.up ℤ) i).hom.app _ ≫
(homology_functor (Condensed.{u} Ab.{u+1}) (complex_shape.up ℤ) i).map
(eval_freeCond'_iso_component _ _).inv

-- Key Lemma
instance is_iso_tensor_to_homology (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  is_iso (tensor_to_homology BD M i) :=
begin
  /-
  rw is_iso_iff_ExtrDisc, intros S,
  rw tensor_to_homology_val_eq, simp_rw ← category.assoc,
  apply_with is_iso.comp_is_iso { instances := ff },
  swap, { sorry }, -- easy
  apply_with is_iso.comp_is_iso { instances := ff },
  swap, { sorry }, -- easy
  -/
  sorry
end

-- needs torsion-free condition on `M`
def homology_bd_eval (M : Condensed.{u} Ab.{u+1})
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (M.val.obj (op S.val))] (i : ℤ) :
  ((BD.eval freeCond').obj M).val.as.homology i ≅
  (tensor M $ ((BD.eval $
    category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
      (AddCommGroup.free.obj punit)).val.as.homology i) :=
(as_iso $ tensor_to_homology BD M i).symm

instance : has_coproducts (endomorphisms (Condensed.{u} Ab.{u+1})) :=
sorry

instance : AB4 (endomorphisms (Condensed.{u} Ab.{u+1})) :=
sorry

def eval_freeCond_homology_zero :
  ((data.eval_functor freeCond').obj breen_deligne.eg.data) ⋙ homology_functor _ _ 0 ≅ 𝟭 _ :=
sorry

instance (α : Type (u+1)) (M) :
  preserves_colimits_of_shape (discrete α) (endo_tensor.obj M) :=
sorry

lemma bd_lemma (A : Condensed.{u} Ab.{u+1}) (B : Condensed.{u} Ab.{u+1})
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
