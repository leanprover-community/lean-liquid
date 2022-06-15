import breen_deligne.main
import breen_deligne.eg
import condensed.tensor
import condensed.evaluation_homology
import pseudo_normed_group.QprimeFP

.

noncomputable theory

universes u

open category_theory category_theory.limits breen_deligne opposite
open bounded_homotopy_category

namespace Condensed

variables (BD : package)

def tensor_to_homology_bd_eval_component (M : Condensed.{u} Ab.{u+1}) (i : ℤ)
  (S : ExtrDisc.{u}) :
  M.val.obj (op S.val) ⟶
  AddCommGroup.of
    (((BD.eval (forget AddCommGroup ⋙ AddCommGroup.free)).obj
      (AddCommGroup.free.obj punit)).val.as.homology i ⟶
      homology ((((BD.eval freeCond').obj M).val.as.d_to i).val.app (op S.val))
        ((((BD.eval freeCond').obj M).val.as.d_from i).val.app (op S.val)) begin
          rw [← nat_trans.comp_app, ← Sheaf.hom.comp_val, homological_complex.d_to_comp_d_from],
          refl,
        end) :=
{ to_fun := λ m, homology.desc' _ _ _
    (homology.lift _ _ _
    (kernel.ι _ ≫
    begin
      rcases i with (_|_)|_,
      -- (AT): This is the general idea to construct this map.
      -- this should be pulled out into separate declarations,
      -- one for i = 0, for i > 0 and for i < 0.
      refine _ ≫ (proetale_topology.to_sheafify _).app _,
      dsimp [package.eval],
      apply AddCommGroup.free.map,
      let e : (⨁ λ (i : ulift (fin (BD.data.X 0))), M).val.obj (op S.val) ≅
        ⨁ (λ i : ulift (fin (BD.data.X 0)), M.val.obj (op S.val)) :=
        (Condensed.evaluation Ab.{u+1} S.val).map_biproduct
          (λ (i : ulift (fin (BD.data.X 0))), M),
      refine _ ≫ (category_theory.forget _).map e.inv,
      apply (category_theory.forget _).map,
      refine biproduct.map _,
      intros j,
      refine (AddCommGroup.adj.hom_equiv _ _).symm _,
      exact (λ _, m),
      { sorry },
      { sorry }
    end
    ≫ cokernel.π _) sorry) sorry,
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
    exact tensor_to_homology_bd_eval_component BD M i S.unop,
  end,
  naturality' := sorry })

-- needs torsion-free condition on `M`
def homology_bd_eval (M : Condensed.{u} Ab.{u+1}) (i : ℤ) :
  ((BD.eval freeCond').obj M).val.as.homology i ≅
  (tensor M $ ((BD.eval $
    category_theory.forget AddCommGroup ⋙ AddCommGroup.free').obj
      (AddCommGroup.of $ punit →₀ ℤ)).val.as.homology i) :=
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
