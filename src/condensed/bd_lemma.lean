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
import condensed.short_exact
import for_mathlib.free_abelian_exact

.

noncomputable theory

universes u

open category_theory category_theory.limits breen_deligne opposite
open_locale big_operators

section
open category_theory.preadditive

attribute [simps map] AddCommGroup.free

lemma oof (A B : AddCommGroup.{u}) : (A →+ B) = (A ⟶ B) := rfl

lemma reorder {M : Type*} [add_comm_monoid M] (a b c d : M) :
  (a + b) + (c + d) = (a + c) + (b + d) :=
by { simp only [add_assoc, add_left_comm b c d], }

def eval_free_π (A : AddCommGroup.{u}) (i : fin 2) : (preadditive.Pow 2).obj A ⟶ (preadditive.Pow 1).obj A :=
biproduct.π _ (ulift.up i) ≫ biproduct.ι (λ _, A) (ulift.up 0)

lemma eval_free_π_eq (A : AddCommGroup.{u}) (k : fin 2) :
  eval_free_π A k = biproduct.matrix
    (λ (i : ulift (fin 2)) (j : ulift (fin 1)), basic_universal_map.proj 1 k j.down i.down • 𝟙 A) :=
begin
  apply biproduct.hom_ext, rintro ⟨j⟩, fin_cases j,
  rw [biproduct.matrix_π, eval_free_π, category.assoc, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl,
    category.comp_id],
  apply biproduct.hom_ext', rintro ⟨i⟩, rw [biproduct.ι_desc],
  suffices : basic_universal_map.proj 1 k 0 i = if i = k then 1 else 0,
  { rw [this, biproduct.ι_π], dsimp, obtain (rfl|hik) := eq_or_ne i k,
    { rw [if_pos rfl, if_pos rfl, one_smul], },
    { rw [if_neg, if_neg hik, zero_smul], intro H, apply hik, apply equiv.ulift.symm.injective, exact H } },
  { dsimp [basic_universal_map.proj, basic_universal_map.proj_aux], dec_trivial! },
end

def eval_free_σ (A : AddCommGroup.{u}) : (preadditive.Pow 2).obj A ⟶ (preadditive.Pow 1).obj A :=
eval_free_π A 0 + eval_free_π A 1

lemma eval_free_d10 (A : AddCommGroup.{u}) :
  (((data.eval_functor (forget _ ⋙ AddCommGroup.free)).obj breen_deligne.eg.data).obj A).d 1 0 =
  ((forget _ ⋙ AddCommGroup.free).map $ eval_free_π A 0) +
  ((forget _ ⋙ AddCommGroup.free).map $ eval_free_π A 1) -
  ((forget _ ⋙ AddCommGroup.free).map $ eval_free_σ A) :=
begin
  dsimp only [eg, eg.BD, data.eval_functor_obj_obj_d], rw [dif_pos rfl],
  dsimp only [universal_map.eval_Pow], rw [lift_app],
  dsimp only [whisker_right_app, eg.map, eg.σπ, universal_map.proj, universal_map.sum],
  simp only [add_monoid_hom.map_sub, free_abelian_group.lift.of,
    basic_universal_map.eval_Pow_app, functor.comp_map, forget_map_eq_coe, sub_comp, add_comp,
    preadditive.Pow_obj, forget_obj_eq_coe, fin.sum_univ_two, add_monoid_hom.map_add],
  refine congr_arg2 _ (congr_arg2 _ _ _) _; congr' 2,
  { rw eval_free_π_eq, refl, },
  { rw eval_free_π_eq, refl, },
  { rw [eval_free_σ, eval_free_π_eq, eval_free_π_eq],
    apply biproduct.hom_ext, rintro ⟨j⟩, fin_cases j, simp only [add_comp, biproduct.matrix_π],
    erw [biproduct.matrix_π, biproduct.matrix_π],
    apply biproduct.hom_ext', rintro ⟨i⟩, simp only [comp_add, biproduct.ι_desc, ← add_smul],
    refl }
end

def Pow_1_iso (A : AddCommGroup.{u}) : (preadditive.Pow 1).obj A ≅ A :=
{ hom := biproduct.π (λ _, A) (ulift.up 0),
  inv := biproduct.ι (λ _, A) (ulift.up 0),
  hom_inv_id' := begin
    erw [← biproduct.total, ← equiv.ulift.symm.sum_comp, fin.sum_univ_one], refl,
  end,
  inv_hom_id' := by simp only [biproduct.ι_π, dif_pos rfl, eq_to_hom_refl] }

def Pow_2_iso (A : AddCommGroup.{u}) : (preadditive.Pow 2).obj A ≅ AddCommGroup.of (A × A) :=
{ hom := add_monoid_hom.prod (biproduct.π (λ _, A) (ulift.up 0)) (biproduct.π (λ _, A) (ulift.up 1)),
  inv := add_monoid_hom.coprod (biproduct.ι (λ _, A) (ulift.up 0)) (biproduct.ι (λ _, A) (ulift.up 1)),
  hom_inv_id' := begin
    ext x, erw [← biproduct.total, ← equiv.ulift.symm.sum_comp, comp_apply],
    swap, apply_instance,
    dsimp only [add_monoid_hom.coprod_apply, add_monoid_hom.prod_apply],
    simp only [← comp_apply, fin.sum_univ_two], refl,
  end,
  inv_hom_id' := begin
    ext1 x, rw [comp_apply, id_apply],
    dsimp only [add_monoid_hom.coprod_apply, add_monoid_hom.prod_apply],
    simp only [add_monoid_hom.map_add, ← comp_apply, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl, id_apply],
    rw [dif_neg], swap, dec_trivial,
    rw [dif_neg], swap, dec_trivial,
    erw [add_zero, zero_add], cases x, refl,
  end }
.

lemma eval_free_π_eq_fst (A : AddCommGroup.{u}) :
  (Pow_2_iso A).inv ≫ eval_free_π A 0 ≫ (Pow_1_iso A).hom =
  AddCommGroup.of_hom (add_monoid_hom.fst A A) :=
begin
  ext x, simp only [comp_apply],
  dsimp only [Pow_2_iso, Pow_1_iso, eval_free_π, add_monoid_hom.coprod_apply],
  simp only [← comp_apply, category.assoc, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl,
    category.comp_id, add_monoid_hom.map_add, id_apply],
  erw [dif_neg, add_zero], refl, dec_trivial,
end

lemma eval_free_π_eq_snd (A : AddCommGroup.{u}) :
  (Pow_2_iso A).inv ≫ eval_free_π A 1 ≫ (Pow_1_iso A).hom =
  AddCommGroup.of_hom (add_monoid_hom.snd A A) :=
begin
  ext x, simp only [comp_apply],
  dsimp only [Pow_2_iso, Pow_1_iso, eval_free_π, add_monoid_hom.coprod_apply],
  simp only [← comp_apply, category.assoc, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl,
    category.comp_id, add_monoid_hom.map_add, id_apply],
  erw [dif_neg, zero_add], refl, dec_trivial,
end

lemma eval_free_σ_eq_add (A : AddCommGroup.{u}) :
  (Pow_2_iso A).inv ≫ eval_free_σ A ≫ (Pow_1_iso A).hom =
  AddCommGroup.of_hom (add_monoid_hom.coprod (add_monoid_hom.id _) (add_monoid_hom.id _)) :=
by { simp only [eval_free_σ, add_comp, comp_add, eval_free_π_eq_fst, eval_free_π_eq_snd], refl, }

lemma eval_free_homology_zero_exact (A : AddCommGroup.{u}) :
  exact
  ((((data.eval_functor (forget _ ⋙ AddCommGroup.free)).obj breen_deligne.eg.data).obj A).d 1 0)
  ((forget _ ⋙ AddCommGroup.free).map (Pow_1_iso A).hom ≫ AddCommGroup.of_hom (free_abelian_group.lift id)) :=
begin
  let F := forget _ ⋙ AddCommGroup.free,
  refine exact_of_iso_of_exact' _ _ _ _
    (F.map_iso (Pow_2_iso A).symm) (F.map_iso (Pow_1_iso A).symm) (iso.refl _) _ _
    (free_abelian_group.exact_σπ A),
  swap,
  { dsimp only [functor.map_iso_hom, iso.symm_hom, iso.refl_hom, F],
    rw [category.comp_id, ← functor.map_iso_inv, ← functor.map_iso_hom, iso.inv_hom_id_assoc], },
  rw [← iso.comp_inv_eq, category.assoc, eval_free_d10],
  simp only [comp_add, add_comp, comp_sub, sub_comp],
  refine congr_arg2 _ (congr_arg2 _ _ _) _,
  { simp only [functor.map_iso_hom, functor.map_iso_inv, iso.symm_hom, iso.symm_inv,
      ← functor.map_comp, eval_free_π_eq_fst], refl },
  { simp only [functor.map_iso_hom, functor.map_iso_inv, iso.symm_hom, iso.symm_inv,
      ← functor.map_comp, eval_free_π_eq_snd], refl },
  { simp only [functor.map_iso_hom, functor.map_iso_inv, iso.symm_hom, iso.symm_inv,
      ← functor.map_comp, eval_free_σ_eq_add], refl },
end

lemma eval_free_homology_zero_surj (A : AddCommGroup) :
  function.surjective ((forget _ ⋙ AddCommGroup.free).map (Pow_1_iso A).hom ≫ free_abelian_group.lift id) :=
begin
  erw [← AddCommGroup.epi_iff_surjective, ← functor.map_iso_hom],
  apply_with epi_comp {instances:=ff}, apply_instance,
  rw [AddCommGroup.epi_iff_surjective], intro a,
  exact ⟨free_abelian_group.of a, free_abelian_group.lift.of _ _⟩
end

def eval_free_homology_zero :
  ((data.eval_functor (forget _ ⋙ AddCommGroup.free)).obj breen_deligne.eg.data) ⋙ homology_functor _ _ 0 ≅ 𝟭 _ :=
-- on objects, use `eval_free_homology_zero_exact` and `eval_free_homology_zero_surj`
sorry

end

open bounded_homotopy_category

namespace Condensed

variables (BD : package)

def eval_freeCond_homology_zero :
  ((data.eval_functor freeCond').obj breen_deligne.eg.data) ⋙ homology_functor _ _ 0 ≅ 𝟭 _ :=
-- rewrite with isoms to reduce to checking on presheaves,
-- then use `eval_free_homology_zero`
sorry

def tensor_punit :
  tensor_functor.flip.obj (AddCommGroup.of (punit →₀ ℤ)) ≅ 𝟭 _ :=
sorry

lemma tensor_short_exact (A : (Condensed.{u} Ab.{u+1}))
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (A.val.obj (op S.val))]
  {X Y Z : Ab} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : short_exact f g) :
  short_exact ((tensor_functor.obj A).map f) ((tensor_functor.obj A).map g) :=
sorry

lemma bd_lemma (A : Condensed.{u} Ab.{u+1}) (B : Condensed.{u} Ab.{u+1})
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (A.val.obj (op S.val))]
  (f : A ⟶ A) (g : B ⟶ B) :
  (∀ i, is_iso $ ((Ext' i).map f.op).app B - ((Ext' i).obj (op A)).map g) ↔
  (∀ i, is_iso $
    ((Ext i).map ((breen_deligne.eg.eval freeCond').map f).op).app ((single _ 0).obj B) -
    ((Ext i).obj (op $ (breen_deligne.eg.eval freeCond').obj A)).map ((single _ 0).map g)) :=
begin
  refine eg.main_lemma' _ A B f g
    eval_freeCond_homology_zero tensor_functor tensor_punit _ _,
  { intros X Y Z _ _ h, refine tensor_short_exact _ _ _ h, },
  { intros t ht,
    let HtQ'Z := ((eg.eval $
      category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
        (AddCommGroup.free.obj punit)).val.as.homology t,
    refine ⟨HtQ'Z, ⟨_⟩⟩,
    -- somehow, use `homology_bd_eval`
    sorry }
end

end Condensed
