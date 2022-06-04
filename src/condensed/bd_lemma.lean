import breen_deligne.main
import condensed.tensor
import pseudo_normed_group.QprimeFP

noncomputable theory

universes u

open category_theory breen_deligne opposite
open bounded_homotopy_category

namespace condensed

variables (BD : package)

lemma bd_lemma (A : Condensed.{u} Ab.{u+1}) (B : Condensed.{u} Ab.{u+1})
  (f : A ⟶ A) (g : B ⟶ B)
  (hH0 : (((data.eval_functor freeCond').obj BD.data).obj A).homology 0 ≅ A) :
  (∀ i, is_iso $ ((Ext' i).map f.op).app B - ((Ext' i).obj (op A)).map g) ↔
  (∀ i, is_iso $
    ((Ext i).map ((BD.eval freeCond').map f).op).app ((single _ 0).obj B) -
    ((Ext i).obj (op $ (BD.eval freeCond').obj A)).map ((single _ 0).map g)) :=
begin
  apply package.main_lemma;
  sorry
end

end condensed
