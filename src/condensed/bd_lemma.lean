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
def plain_eval_comparison (i : ℤ) :
  AddCommGroup.tensor_functor.flip.obj
  (((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).homology i) ⟶
  BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free) ⋙ homology_functor _ _ i :=
sorry
-/

/-
WARNING!!!: I don't think this is the best approach...

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

instance is_iso_tensor_to_homology_aux₁ (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
is_iso ((Condensed_ExtrSheafProd_equiv _).inverse.map
  (ExtrSheafProd.tensor_uncurry (uncurried_tensor_to_homology BD M i))) := sorry

/-
-- Key Lemma
instance is_iso_tensor_to_homology_aux (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  is_iso (ExtrSheafProd.tensor_uncurry (uncurried_tensor_to_homology BD M i)) :=
begin
  suffices : is_iso
  suffices : is_iso (ExtrSheafProd.tensor_uncurry (uncurried_tensor_to_homology BD M i)).val,
  { let t := _, change is_iso t,
    change is_iso ((ExtrSheafProd_to_presheaf _).map t) at this,
    resetI,
    apply is_iso_of_fully_faithful (ExtrSheafProd_to_presheaf Ab.{u+1}) },
  apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
  intros S, dsimp [ExtrSheafProd.tensor_uncurry],
end
-/

instance is_iso_tensor_to_homology (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  is_iso (tensor_to_homology BD M i) :=
begin
  apply is_iso.comp_is_iso,
end
-/

def point {A : Type u} (a : A) : punit.{u+1} ⟶ A := λ _, a

def tensor_to_unsheafified_homology_component_applied
  (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S : ExtrDisc.{u}) (m : M.val.obj (op S.val)) :
  ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as.homology i ⟶
  (homological_complex.homology ((BD.eval' freeFunc).obj
    (Condensed_Ab_to_presheaf.obj M)) i).obj (op S.val) :=
match i with
| (int.of_nat 0) := (homology_functor _ _ _).map
    ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).map
      ((AddCommGroup.adj.hom_equiv _ _).symm (point m)) ≫
      (eval_freeAb_iso_component _ _ _).inv) ≫
    (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
      (op S.val)).homology_functor_iso _ _).inv.app _
| (int.of_nat (i+1)) := 0
| (int.neg_succ_of_nat i) := (homology_functor _ _ _).map
    ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).map
      ((AddCommGroup.adj.hom_equiv _ _).symm (point m)) ≫
      (eval_freeAb_iso_component _ _ _).inv) ≫
    (((category_theory.evaluation Profinite.{u}ᵒᵖ Ab.{u+1}).obj
      (op S.val)).homology_functor_iso _ _).inv.app _
end

def tensor_to_unsheafified_homology_component (M : Condensed.{u} Ab.{u+1}) (i : ℤ)
  (S : ExtrDisc.{u}) :
  M.val.obj (op S.val) ⟶
  AddCommGroup.of
    (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i ⟶
    (homological_complex.homology ((BD.eval' freeFunc).obj
      (Condensed_Ab_to_presheaf.obj M)) i).obj (op S.val)) :=
{ to_fun := λ m, tensor_to_unsheafified_homology_component_applied _ _ _ _ m,
  map_zero' := sorry,
  map_add' := sorry }

def tensor_to_unsheafified_homology (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  (((Condensed_ExtrSheaf_equiv Ab).inverse.obj M).tensor
    (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as.homology i)).val ⟶
  ExtrDisc_to_Profinite.op ⋙ homological_complex.homology
    ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M)) i :=
{ app := λ S, AddCommGroup.tensor_uncurry $
    tensor_to_unsheafified_homology_component _ _ _ _,
  naturality' := sorry }

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

-- needs torsion-free condition on `M`
def homology_bd_eval (M : Condensed.{u} Ab.{u+1})
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (M.val.obj (op S.val))] (i : ℤ) :
  ((BD.eval freeCond').obj M).val.as.homology i ≅
  (tensor M $ ((BD.eval $
    category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
      (AddCommGroup.free.obj punit)).val.as.homology i) :=
sorry

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
