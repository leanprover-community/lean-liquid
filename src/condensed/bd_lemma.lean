import breen_deligne.main
import breen_deligne.eg
import condensed.tensor
import condensed.evaluation_homology
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

def eval_forget_free_eval_to_evaluation_map_eval_freeCond'
  (M : Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) :
  (BD.eval $ category_theory.forget _ ⋙ AddCommGroup.free).obj (M.val.obj (op S.val)) ⟶
  (Condensed.evaluation _ S.val).map_bounded_homotopy_category.obj
  ((BD.eval freeCond').obj M) :=
(homotopy_category.quotient _ _).map
{ f := λ i, begin
    rcases i with (_|_)|_,
    { dsimp [package.eval],
      refine _ ≫ (proetale_topology.to_sheafify _).app _,
      dsimp,
      refine AddCommGroup.free.map _,
      refine (category_theory.forget Ab.{u+1}).map _,
      exact ((Condensed.evaluation Ab.{u+1} S.val).map_biproduct
        (λ (i : ulift (fin (BD.data.X 0))), M)).inv },
    { exact 0 },
    { sorry } -- similar to the zero case.
    -- Again, this should be broken up...
  end,
  comm' := sorry }

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
  let t₂ : _ ≅ (((BD.eval freeCond').obj M).val.as.homology i).val.obj (op S.val) :=
    (Condensed.homology_functor_evaluation_iso _ _ _).symm.app _,
  let s := sorry, -- this needs to be of the form `η.app (M.val.obj (op S))` where
    -- `η` is some natural transformation.
  have hs : t = t₁.hom ≫ s ≫ t₂.hom, sorry,
  dsimp at s,
  suffices : is_iso s,
  { rw hs, resetI, apply_instance },
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

-- needs torsion-free condition on `M`
def homology_bd_eval (M : Condensed.{u} Ab.{u+1})
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (M.val.obj (op S.val))] (i : ℤ) :
  ((BD.eval freeCond').obj M).val.as.homology i ≅
  (tensor M $ ((BD.eval $
    category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
      (AddCommGroup.free.obj punit)).val.as.homology i) :=
(as_iso $ tensor_to_homology_bd_eval BD M i).symm

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
