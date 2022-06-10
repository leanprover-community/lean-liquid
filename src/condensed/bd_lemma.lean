import breen_deligne.main
import breen_deligne.eg
import condensed.tensor
import pseudo_normed_group.QprimeFP

noncomputable theory

universes u

open category_theory category_theory.limits breen_deligne opposite
open bounded_homotopy_category

namespace condensed

variables (BD : package)

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

end condensed
