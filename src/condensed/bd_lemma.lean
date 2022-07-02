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

-- Move this.
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

def plain_eval_comparison_component (i : ℤ) (A : AddCommGroup.{u+1}) :
  A ⟶ AddCommGroup.of
  (homological_complex.homology
    ((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj (AddCommGroup.free.obj punit)) i ⟶
    homological_complex.homology
    ((BD.eval' (category_theory.forget AddCommGroup ⋙ AddCommGroup.free)).obj A) i) :=
{ to_fun := λ a,
    (homology_functor _ _ _).map $ (BD.eval' _).map $ (AddCommGroup.adj.hom_equiv _ _).symm
    (point a),
  map_zero' := sorry,
  map_add' := sorry }

def plain_eval_comparison (i : ℤ) :
  AddCommGroup.tensor_functor.flip.obj
  (((BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).homology i) ⟶
  BD.eval' (forget AddCommGroup ⋙ AddCommGroup.free) ⋙ homology_functor _ _ i :=
{ app := λ A, AddCommGroup.tensor_uncurry $ plain_eval_comparison_component _ _ _,
  naturality' := sorry }

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
sorry

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

instance preserves_filtered_colimits_eval'_forget_free :
  preserves_filtered_colimits.{u+1 u+2 u+2}
    (BD.eval' (forget.{u+2 u+1 u+1} AddCommGroup.{u+1} ⋙ AddCommGroup.free.{u+1})) :=
begin
  apply_with limits.comp_preserves_filtered_colimits.{u+1 u+2 _ u+2} {instances:=ff},
  { apply_with data.eval_functor_preserves_filtered_colimits {instances:=ff},
    apply_with limits.comp_preserves_filtered_colimits.{u+1 u+2 _ u+2} {instances:=ff},
    { apply_instance },
    { sorry } },
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

instance (i : ℤ) : is_iso ((plain_eval_comparison BD i).app
  (AddCommGroup.free.obj (punit : Type (u+1)))) := sorry

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

instance : AB4.{u+1 u+2} (endomorphisms (Condensed.{u} Ab.{u+1})) := sorry

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
