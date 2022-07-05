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
import for_mathlib.homology_exact
import condensed.Qprime_isoms

.

noncomputable theory

universes u

open category_theory category_theory.limits breen_deligne opposite
open_locale big_operators

section
open category_theory.preadditive

attribute [simps map] AddCommGroup.free

lemma oof (A B : AddCommGroup.{u}) : (A →+ B) = (A ⟶ B) := rfl

def eval_free_homology_zero_exact (A : AddCommGroup.{u}) :
  exact
  ((((data.eval_functor (forget _ ⋙ AddCommGroup.free)).obj breen_deligne.eg.data).obj A).d 1 0)
  (free_abelian_group.lift id) :=
begin
  rw AddCommGroup.exact_iff', split,
  { dsimp only [eg, eg.BD, data.eval_functor_obj_obj_d], rw [dif_pos rfl],
    dsimp only [universal_map.eval_Pow], rw [lift_app],
    dsimp only [whisker_right_app, eg.map, eg.σπ, universal_map.proj, universal_map.sum],
    simp only [add_monoid_hom.map_sub, add_monoid_hom.map_sum, free_abelian_group.lift.of,
      basic_universal_map.eval_Pow_app, functor.comp_map, forget_map_eq_coe, sub_comp, sum_comp,
      preadditive.Pow_obj, forget_obj_eq_coe],

    ext (x : ((preadditive.Pow 2).obj A : AddCommGroup.{u})),
    have hx := id_apply x,
    erw [← biproduct.total, ← equiv.ulift.symm.sum_comp] at hx, swap, apply_instance,
    rw [← add_monoid_hom.eval_apply_apply, add_monoid_hom.map_sub, add_monoid_hom.map_sum,
      AddCommGroup.zero_apply, ← hx],
    simp only [add_monoid_hom.eval_apply_apply, comp_apply,
      free_abelian_group.lift.of, free_abelian_group.lift_id_map, AddCommGroup.free_map],
    simp only [← comp_apply, sum_comp, category.assoc, biproduct.ι_matrix],
    simp only [fin.sum_univ_two, ← comp_apply, ← add_monoid_hom.add_apply, ← add_monoid_hom.sub_apply],
    conv_rhs { rw [← AddCommGroup.zero_apply ((preadditive.Pow 2).obj A) ((preadditive.Pow 1).obj A) x], },
    congr' 1,
    dsimp only [oof],
    apply biproduct.hom_ext, intro j,
    simp only [sub_comp, add_comp, biproduct.lift_π, category.assoc, zero_comp],
    sorry },
  { sorry }
end

def eval_free_homology_zero_surj (A : AddCommGroup) :
  function.surjective (free_abelian_group.lift (id : A → A)) :=
λ a, ⟨free_abelian_group.of a, free_abelian_group.lift.of _ _⟩

def eval_free_homology_zero :
  ((data.eval_functor (forget _ ⋙ AddCommGroup.free)).obj breen_deligne.eg.data) ⋙ homology_functor _ _ 0 ≅ 𝟭 _ :=
sorry

end

open bounded_homotopy_category

namespace Condensed

variables (BD : package)

def eval_freeCond_homology_zero :
  ((data.eval_functor freeCond').obj breen_deligne.eg.data) ⋙ homology_functor _ _ 0 ≅ 𝟭 _ :=
sorry

instance endo_tensor_preserves_colimits_of_shape (α : Type (u+1)) (M) :
  preserves_colimits_of_shape (discrete α) (endo_tensor.obj M) :=
begin
  haveI : reflects_colimits_of_shape (discrete α) (endomorphisms.forget
    (Condensed.{u} Ab.{u+1})) := { },
  haveI : preserves_colimits_of_shape (discrete α) (endo_tensor.obj M
    ⋙ endomorphisms.forget (Condensed.{u} Ab.{u+1})),
  { apply preserves_colimits_of_shape_of_nat_iso (endo_tensor_comp_forget M).symm,
    apply_instance, },
  exact preserves_colimits_of_shape_of_reflects_of_preserves
    (endo_tensor.obj M) (endomorphisms.forget _),
end

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
