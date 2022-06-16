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

/-
def component_aux_pos (M : Condensed.{u} Ab.{u+1}) (i : ℕ) (S : Profinite.{u}) :
  ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as.X (i+1) ⟶
  (((BD.eval freeCond').obj M).val.as.X (i+1)).val.obj (op S) := 0

def component_aux_neg (M : Condensed.{u} Ab.{u+1}) (i : ℕ) (S : Profinite.{u})
  (m : M.val.obj (op S)) :
  ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as.X (-[1+i]) ⟶
  (((BD.eval freeCond').obj M).val.as.X (-[1+i])).val.obj (op S) :=
begin
  refine _ ≫ (proetale_topology.to_sheafify _).app _,
  apply AddCommGroup.free.map,
  let e : (⨁ λ (j : ulift (fin (BD.data.X (i+1)))), M).val.obj (op S) ≅
    ⨁ (λ j : ulift (fin (BD.data.X (i+1))), M.val.obj (op S)) :=
    (Condensed.evaluation Ab.{u+1} S).map_biproduct
      (λ (j : ulift (fin (BD.data.X (i+1)))), M),
  refine _ ≫ (category_theory.forget _).map e.inv,
  apply (category_theory.forget _).map,
  refine biproduct.map _,
  intros j,
  refine (AddCommGroup.adj.hom_equiv _ _).symm _,
  exact (λ _, m),
end

def component_aux_zero (M : Condensed.{u} Ab.{u+1}) (S : Profinite.{u})
  (m : M.val.obj (op S)) :
  ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as.X 0 ⟶
  (((BD.eval freeCond').obj M).val.as.X 0).val.obj (op S) :=
begin
  refine _ ≫ (proetale_topology.to_sheafify _).app _,
  apply AddCommGroup.free.map,
  let e : (⨁ λ (j : ulift (fin (BD.data.X 0))), M).val.obj (op S) ≅
    ⨁ (λ j : ulift (fin (BD.data.X 0)), M.val.obj (op S)) :=
    (Condensed.evaluation Ab.{u+1} S).map_biproduct
      (λ (j : ulift (fin (BD.data.X 0))), M),
  refine _ ≫ (category_theory.forget _).map e.inv,
  apply (category_theory.forget _).map,
  refine biproduct.map _,
  intros j,
  refine (AddCommGroup.adj.hom_equiv _ _).symm _,
  exact (λ _, m),
end

def component_aux (M : Condensed.{u} Ab.{u+1}) (S : Profinite.{u})
  (m : M.val.obj (op S)) (i : ℤ) :
  ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as.X i ⟶
  (((BD.eval freeCond').obj M).val.as.X i).val.obj (op S) :=
match i with
| int.of_nat 0 := component_aux_zero _ _ _ m
| int.of_nat (i+1) := 0
| -[1+i] := component_aux_neg _ _ _ _ m
end

def tensor_to_homology_bd_eval_component (M : Condensed.{u} Ab.{u+1}) (i : ℤ)
  (S : Profinite.{u}) (w) :
  M.val.obj (op S) ⟶
  AddCommGroup.of
    (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i ⟶
      homology ((((BD.eval freeCond').obj M).val.as.d_to i).val.app (op S))
        ((((BD.eval freeCond').obj M).val.as.d_from i).val.app (op S)) w) :=
{ to_fun := λ m, homology.desc' _ _ _
    (homology.lift _ _ _
    (kernel.ι _ ≫ component_aux _ _ _ m _ ≫ cokernel.π _) sorry) sorry,
  map_zero' := sorry,
  map_add' := sorry }

def tensor_to_homology_bd_eval (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  (tensor M $ ((BD.eval $
    category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
      (AddCommGroup.free.obj punit)).val.as.homology i) ⟶
  ((BD.eval freeCond').obj M).val.as.homology i :=
tensor_uncurry $
((Condensed_ExtrSheafProd_equiv _).unit_iso.app _).hom ≫
(Condensed_ExtrSheafProd_equiv _).inverse.map
(ExtrSheafProd.hom.mk
{ app := λ S, begin
    dsimp,
    refine _ ≫ (preadditive_yoneda.flip.obj
      (opposite.op (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i))).map
      (homology_evaluation_iso _ _ _ _).inv,
    --now we need to produce some map between two homology groups.
    exact tensor_to_homology_bd_eval_component BD M i S.unop.val _,
  end,
  naturality' := sorry })

instance is_iso_tensor_to_homology_bd_eval_eval_ExtrDisc
  (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S : ExtrDisc.{u})
  [no_zero_smul_divisors ℤ (M.val.obj (op S.val))] :
  is_iso ((tensor_to_homology_bd_eval BD M i).val.app (op S.val)) :=
begin
  -- Key: Use `AddCommGroup.is_iso_of_preserves_of_is_tensor_unit`,
  let t := _, change is_iso t,
  let t₁ :
    (M.tensor (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i)).val.obj (op S.val) ≅
    (M.val.obj (op S.val)).tensor _ :=
    tensor_eval_iso M (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i) S,
  let s := sorry, -- this needs to be of the form `η.app (M.val.obj (op S))` where
    -- `η` is some natural transformation.
  have hs : t = t₁.hom ≫ s, sorry,
  suffices : is_iso s,
  { rw hs, resetI, apply_instance },
  /-
  Now we need to rewrite `s` as well.
  Here `s` is essentially supposed to be an isomorphism from
  `H^i(Q'(ℤ)) ⊗ M(S)` to `H^i(Q'(M))(S)`.
  Recall, `Q'(M)` is some BD-like complex:
  `Q'(M) := ⋯ → ℤ[M^n] → ℤ[M^m] → 0`
  defined essentially as applying sheafification to
  `Q'(M)' := ⋯ → ℤ[M^n]' → ℤ[M^m]' → 0.`
  Sheafification is exact so that H^i(Q'(M)) is the sheafification of `H^i(Q'(M)')`, and the
  natural map
  `H^i(Q'(ℤ)) ⊗ M(S) → H^i(Q'(M)')(S) = H^i(Q'(M(S))` is indeed an isomorphism.

  -/
  sorry,
  -- Key: Use `AddCommGroup.is_iso_of_preserves_of_is_tensor_unit`
end

instance is_iso_tensor_to_homology_bd_eval
  (M : Condensed.{u} Ab.{u+1}) (i : ℤ)
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (M.val.obj (op S.val))]:
  is_iso (tensor_to_homology_bd_eval BD M i) :=
begin
  rw is_iso_iff_ExtrDisc,
  intros S, apply_instance,
end
-/

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

def eval_freeCond'_iso :
  BD.eval' freeCond' ≅
  Condensed_Ab_to_presheaf ⋙
  BD.eval' freeFunc ⋙
  presheaf_to_Condensed_Ab.map_homological_complex _ :=
nat_iso.of_components
(λ M, eval_freeCond'_iso_component _ _)
sorry

def eval_comparison (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) (m : M.val.obj (op S.val)) :
  ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as ⟶
  ((evaluation AddCommGroup S.val).map_homological_complex (complex_shape.up ℤ)).obj
    ((presheaf_to_Condensed_Ab.map_homological_complex (complex_shape.up ℤ)).obj
       ((BD.eval freeFunc).obj (Condensed_Ab_to_presheaf.obj M)).val.as) :=
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

def curried_tensor_to_homology_ExtrDisc_component_apply'
  (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S : ExtrDisc.{u}) (m : M.val.obj (op S.val)) :
  ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as.homology i ⟶
  (((evaluation Ab S.val).map_homological_complex (complex_shape.up ℤ)).obj
    ((BD.eval freeCond').obj M).val.as).homology i :=
(homology_functor _ _ _).map (eval_comparison _ _ _ m)
≫ (homology_functor _ _ _).map
  (((evaluation _ _).map_homological_complex _).map $ (eval_freeCond'_iso_component _ _).inv)

def curried_tensor_to_homology_ExtrDisc_component_apply
  (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S : ExtrDisc.{u}) (m : M.val.obj (op S.val)) :
  ((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
    (AddCommGroup.free.obj punit)).val.as.homology i ⟶
  (((BD.eval freeCond').obj M).val.as.homology i).val.obj (op S.val) :=
let e := eval_freeCond'_iso_component BD M in
curried_tensor_to_homology_ExtrDisc_component_apply' _ _ _ _ m
≫ (homology_functor_evaluation_iso _ _ _).inv.app _

def curried_tensor_to_homology_ExtrDisc_component (M : Condensed.{u} Ab.{u+1}) (i : ℤ)
  (S : ExtrDisc.{u}) :
  M.val.obj (op S.val) ⟶
  AddCommGroup.of
    (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i ⟶
      (((BD.eval freeCond').obj M).val.as.homology i).val.obj (op S.val)) :=
{ to_fun := λ m, curried_tensor_to_homology_ExtrDisc_component_apply _ _ _ _ m,
  map_zero' := sorry,
  map_add' := sorry }

def curried_tensor_to_homology_ExtrDisc (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
(Condensed_ExtrSheafProd_equiv Ab).functor.obj M ⟶
  ExtrSheafProd.half_internal_hom
    (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i)
    ((Condensed_ExtrSheafProd_equiv Ab).functor.obj
      (((BD.eval freeCond').obj M).val.as.homology i)) :=
ExtrSheafProd.hom.mk $
{ app := λ S, curried_tensor_to_homology_ExtrDisc_component _ _ _ S.unop,
  naturality' := sorry }

def curried_tensor_to_homology (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  M ⟶
  half_internal_hom
    (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i)
    (((BD.eval freeCond').obj M).val.as.homology i) :=
((Condensed_ExtrSheafProd_equiv _).unit_iso.app _).hom  ≫
(Condensed_ExtrSheafProd_equiv _).inverse.map
(curried_tensor_to_homology_ExtrDisc _ _ _)

def tensor_to_homology (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  M.tensor (((BD.eval $
    category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
      (AddCommGroup.free.obj punit)).val.as.homology i) ⟶
  ((BD.eval freeCond').obj M).val.as.homology i :=
tensor_uncurry (curried_tensor_to_homology _ _ _)

def tensor_to_unsheafified_homology_component
  (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S : ExtrDisc.{u}) :
  (M.tensor (((BD.eval $
    category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
      (AddCommGroup.free.obj punit)).val.as.homology i)).val.obj (op S.val) ⟶
  (((BD.eval freeFunc).obj M.val).val.as.homology i).obj (op S.val) :=
(tensor_eval_iso _ _ _).hom ≫
AddCommGroup.tensor_uncurry sorry ≫
(((category_theory.evaluation Profinite.{u}ᵒᵖ
  Ab.{u+1}).obj (op S.val)).homology_functor_iso (complex_shape.up ℤ) i).inv.app _

lemma tensor_to_homology_val_eq (M : Condensed.{u} Ab.{u+1}) (i : ℤ) (S : ExtrDisc.{u}) :
  (tensor_to_homology BD M i).val.app (op S.val) =
  tensor_to_unsheafified_homology_component _ _ _ _ ≫
    (proetale_topology.to_sheafify _ ≫
    ((homology_functor_sheafification_iso (complex_shape.up ℤ) i).hom.app _).val ≫
    Condensed_Ab_to_presheaf.map ((homology_functor _ _ _).map
    (eval_freeCond'_iso_component _ _).inv)).app _ :=
sorry

-- Key Lemma
instance is_iso_tensor_to_homology (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  is_iso (tensor_to_homology BD M i) :=
begin
  rw is_iso_iff_ExtrDisc, intros S,
  simp_rw [tensor_to_homology_val_eq, nat_trans.comp_app, ← category.assoc],
  apply_with is_iso.comp_is_iso { instances := ff },
  swap, apply_instance,
  apply_with is_iso.comp_is_iso { instances := ff },
  swap,
  { apply_with nat_iso.is_iso_app_of_is_iso { instances := ff },
    let t := (homology_functor_sheafification_iso (complex_shape.up ℤ) i).hom.app
      ((BD.eval freeFunc).obj M.val).val.as,
    suffices : is_iso (Condensed_Ab_to_presheaf.map t),
    { exact this },
    apply_instance },

  -- TODO: reorrganize the previous argument... the next goal is not provable, but
  -- it will be enough given the sketch above.
  -- This is the interesting part.
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
