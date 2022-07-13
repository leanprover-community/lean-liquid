import Lbar.ext_aux3
import Lbar.iota

noncomputable theory

universes v u u'

open opposite category_theory category_theory.limits category_theory.preadditive
open_locale nnreal zero_object

variables (r r' : ℝ≥0)
variables [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]

open bounded_homotopy_category

variables {r'}
variables (BD : breen_deligne.package)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.data.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

section preps

variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]
variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

set_option pp.universes true

lemma homotopy_category.colimit_cofan_bdd {A : Type u} [category.{v} A] [abelian A]
[has_coproducts A] {α : Type v} (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] : homotopy_category.is_bounded_above
  (homotopy_category.colimit_cofan $ λ a : α, (X a).val).X :=
begin
    obtain ⟨n,hn⟩ := homotopy_category.is_uniformly_bounded_above.cond (val ∘ X),
      use n, intros i hi,
    dsimp [homotopy_category.colimit_cofan],
    let e : (∐ λ (a : α), (X a).val.as).X i ≅
      (∐ λ (a : α), (X a).val.as.X i) := homotopy_category.coproduct_iso _ _,
    refine is_zero_of_iso_of_zero _ e.symm,
    apply category_theory.is_zero_colimit,
    intros j,
    apply hn j _ hi,
  end

def Tinv2_iso_of_bicartesian_aux_1
  (i : ℤ) : commsq.{u+2 u+1}
  (shift_sub_id.{u+1}
     ((QprimeFP.{u} r' BD.data κ₂ M).op ⋙
        (Ext.{u+1 u+2} i).flip.obj ((single.{u+1 u+2} (Condensed.{u u+1 u+2} Ab.{u+1}) 0).obj V.to_Cond))
     ι
     hι)
  (pi_Ext_iso_Ext_sigma.{u} BD κ₂ M V (λ (k : ulift.{u+1 0} ℕ), ι k) i).hom
  (pi_Ext_iso_Ext_sigma.{u} BD κ₂ M V (λ (k : ulift.{u+1 0} ℕ), ι k) i).hom
  (((Ext.{u+1 u+2} i).map
      (of_hom.{u+1 u+2} (QprimeFP.shift_sub_id.{u u+2 u+1} ι hι (QprimeFP_int.{u} r' BD.data κ₂ M))).op).app
     ((single.{u+1 u+2} (Condensed.{u u+1 u+2} Ab.{u+1}) 0).obj (Condensed.of_top_ab.{u} ↥V))) :=
begin
    apply commsq.of_eq,
    dsimp only [shift_sub_id, QprimeFP.shift_sub_id],
    simp only [sub_comp, comp_sub, homological_complex.of_hom_sub, category_theory.op_sub,
      functor.map_sub, op_id, category_theory.functor.map_id, of_hom_id,
      nat_trans.app_sub, nat_trans.id_app, category.comp_id, category.id_comp],
    apply congr_arg2 _ _ rfl,
    rw ← iso.eq_comp_inv,
    dsimp only [pi_Ext_iso_Ext_sigma, iso.trans_hom, iso.trans_inv,
      iso.symm_hom, iso.symm_inv, functor.map_iso_hom,
      iso.op_hom, op_comp, functor.flip_obj_map, functor.map_iso_inv],
    simp only [category.assoc, ← nat_trans.comp_app_assoc, ← functor.map_comp_assoc,
      ← functor.map_comp, iso.op_inv, ← op_comp],
    rw cofan_point_iso_colimit_conj_eq_desc,
    rw iso.eq_inv_comp,
    have := Ext_coproduct_iso_naturality_shift _
      (λ (k : ulift ℕ), (QprimeFP r' BD.data κ₂ M).obj (ι k))
      (λ k, (QprimeFP r' BD.data κ₂ M).map (hom_of_le $ hι $
        by exact_mod_cast k.down.le_succ)) i ((single (Condensed Ab) 0).obj V.to_Cond),
    exact this.symm,
    { apply homotopy_category.colimit_cofan_bdd },
end

@[reassoc]
lemma Ext_coproduct_iso_π
  (A : Type u) [category.{v} A] [abelian A] [enough_projectives A] [has_coproducts A] [AB4 A]
  (X : ulift.{v} ℕ → bounded_homotopy_category A) [uniformly_bounded X] (i : ℤ) (Y) (k) :
  (Ext_coproduct_iso X i Y).hom ≫ pi.π _ k =
  ((Ext i).map $ quiver.hom.op $ sigma.ι _ _).app Y :=
begin
  dsimp only [Ext_coproduct_iso, iso.trans_hom, pi_iso, preadditive_yoneda_coproduct_iso,
    as_iso_hom, preadditive_yoneda_coproduct_to_product],
  simp only [category.assoc, limit.lift_π, limit.lift_π_assoc, fan.mk_π_app],
  dsimp only [Ext_iso, iso.symm_hom, functor.map_iso_hom, functor.map_iso_inv],
  simp only [← functor.map_comp, iso.op_hom, iso.op_inv, ← op_comp],
  dsimp only [Ext, Ext0, functor.comp_map, whiskering_left_obj_map, whisker_left_app,
    functor.flip_map_app, replacement_iso],
  congr' 2,
  simp only [category.assoc, iso.inv_comp_eq, quiver.hom.unop_op, unop_op, op_unop],
  apply lift_unique,
  simp only [category.assoc, iso.inv_comp_eq, quiver.hom.unop_op, unop_op, op_unop],
  erw lift_lifts,
  simp only [uniform_π, colimit.ι_desc, cofan.mk_ι_app, lift_lifts_assoc],
  refl,
end

lemma Tinv2_iso_of_bicartesian_aux_2
  [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (j) {e : (homotopy_category.colimit_cofan.{u+1 u+2}
     (λ (a : ulift.{u+1 0} ℕ),
        ((λ (k : ulift.{u+1 0} ℕ), (QprimeFP.{u} r' BD.data κ₂ M).obj (ι k)) a).val)).X.is_bounded_above } :
  ((cofan.{u+1 u+2} (λ (k : ulift.{u+1 0} ℕ), (QprimeFP.{u} r' BD.data κ₂ M).obj (ι k))).ι.app j ≫
     of_hom.{u+1 u+2} (sigma_map.{u u+2 u+1} ι (QprimeFP_int.Tinv.{u} BD.data κ₂ κ M))) ≫
  (cofan_point_iso_colimit.{u} (λ (k : ulift.{u+1 0} ℕ), (QprimeFP.{u} r' BD.data κ M).obj (ι k))).hom =
  (QprimeFP.Tinv _ _ _ _).app _ ≫
  sigma.ι (λ (k : ulift.{u+1 0} ℕ), (QprimeFP.{u} r' BD.data κ M).obj (ι k)) j :=
begin
  rw [← iso.eq_comp_inv], simp only [category.assoc, cofan_point_iso_colimit,
    colimit.comp_cocone_point_unique_up_to_iso_inv],
  dsimp only [bounded_homotopy_category.cofan, cofan.mk_ι_app, of_hom,
    homotopy_category.colimit_cofan, QprimeFP.Tinv, whisker_right_app,
    chain_complex.to_bounded_homotopy_category, functor.comp_map],
  erw [← (homotopy_category.quotient.{u+1 u+2 0} (Condensed.{u u+1 u+2} Ab.{u+1}) (complex_shape.up.{0} ℤ)).map_comp],
  erw [← (homotopy_category.quotient.{u+1 u+2 0} (Condensed.{u u+1 u+2} Ab.{u+1}) (complex_shape.up.{0} ℤ)).map_comp],
  congr' 1,
  dsimp only [sigma_map],
  erw [colimit.ι_desc],
  refl,
end

lemma Tinv2_iso_of_bicartesian_aux_3
  [∀ c n, fact (κ₂ c n ≤ κ c n)]
  [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (j)
  {e : (homotopy_category.colimit_cofan.{u+1 u+2}
     (λ (a : ulift.{u+1 0} ℕ),
        ((λ (k : ulift.{u+1 0} ℕ), (QprimeFP.{u} r' BD.data κ₂ M).obj (ι k)) a).val)).X.is_bounded_above} :
  (cofan.{u+1 u+2} (λ (k : ulift.{u+1 0} ℕ), (QprimeFP.{u} r' BD.data κ₂ M).obj (ι k))).ι.app j ≫
  of_hom.{u+1 u+2} (sigma_map.{u u+2 u+1} ι (QprimeFP_int.ι.{u} BD.data κ₂ κ M)) ≫
    (cofan_point_iso_colimit.{u} (λ (k : ulift.{u+1 0} ℕ), (QprimeFP.{u} r' BD.data κ M).obj (ι k))).hom =
  (QprimeFP.ι _ κ₂ κ M).app _ ≫
  sigma.ι ((λ (k : ulift.{u+1 0} ℕ), (QprimeFP.{u} r' BD.data κ M).obj (ι k))) j :=
begin
  simp only [← category.assoc], rw [← iso.eq_comp_inv],
  simp only [category.assoc, cofan_point_iso_colimit, colimit.comp_cocone_point_unique_up_to_iso_inv],
  dsimp only [bounded_homotopy_category.cofan, cofan.mk_ι_app, of_hom,
    homotopy_category.colimit_cofan, QprimeFP.ι, whisker_right_app,
    chain_complex.to_bounded_homotopy_category, functor.comp_map],
  erw [← (homotopy_category.quotient.{u+1 u+2 0} (Condensed.{u u+1 u+2} Ab.{u+1}) (complex_shape.up.{0} ℤ)).map_comp],
  erw [← (homotopy_category.quotient.{u+1 u+2 0} (Condensed.{u u+1 u+2} Ab.{u+1}) (complex_shape.up.{0} ℤ)).map_comp],
  congr' 1,
  dsimp only [sigma_map],
  erw [colimit.ι_desc],
  refl,
end

lemma Tinv2_iso_of_bicartesian_aux [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (i : ℤ)
  (H1 : (shift_sub_id.commsq (ExtQprime.Tinv2 r r' BD.data κ κ₂ M V i) ι hι).bicartesian) :
  (Ext_Tinv2_commsq (of_hom (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.Tinv BD.data κ₂ κ M)))
  (of_hom (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.ι BD.data κ₂ κ M)))
  (of_hom (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.Tinv BD.data κ₂ κ M)))
  (of_hom (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.ι BD.data κ₂ κ M)))
  (of_hom (QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD.data κ₂ M)))
  (of_hom (QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD.data κ M)))
  (auux $ commsq_shift_sub_id_Tinv _ _ _ _ _ _)
  (auux $ commsq_shift_sub_id_ι _ _ _ _ _ _)
  ((single _ 0).map (Condensed.of_top_ab_map (normed_group_hom.to_add_monoid_hom (normed_with_aut.T.inv : V ⟶ V)) (normed_group_hom.continuous _)))
  i).bicartesian :=
begin
  have h1 := _, have h2 := _, have h3 := _,
  refine commsq.bicartesian.of_iso
    (pi_Ext_iso_Ext_sigma _ _ _ _ _ _) (pi_Ext_iso_Ext_sigma _ _ _ _ _ _)
    (pi_Ext_iso_Ext_sigma _ _ _ _ _ _) (pi_Ext_iso_Ext_sigma _ _ _ _ _ _)
    h1 h2 h2 h3 H1,
  apply Tinv2_iso_of_bicartesian_aux_1,
  { clear h1, apply commsq.of_eq, rw ← iso.eq_comp_inv,
    apply limit.hom_ext, intros j, rw lim_map_π,
    dsimp [pi_Ext_iso_Ext_sigma],
    simp only [category.assoc],
    have := Ext_coproduct_iso_π _
      (λ (k : ulift.{u+1 0} ℕ), (QprimeFP.{u} r' BD.data κ₂ M).obj (ι k))
      i ((single.{u+1 u+2} (Condensed.{u u+1 u+2} Ab.{u+1}) 0).obj V.to_Cond) j,
    rw [this, ← nat_trans.comp_app, ← functor.map_comp, ← op_comp],
    clear this,
    erw colimit.ι_desc,
    dsimp [Ext_Tinv2, ExtQprime.Tinv2],
    simp only [sub_comp, comp_sub],
    refine congr_arg2 _ _ _,
    { simp only [← nat_trans.comp_app, ← functor.map_comp, ← op_comp],
      rw Tinv2_iso_of_bicartesian_aux_2,
      swap,
      { apply homotopy_category.colimit_cofan_bdd },
      simp only [functor.map_comp, op_comp, nat_trans.comp_app, category.assoc],
      have := Ext_coproduct_iso_π _
        (λ (k : ulift.{u+1 0} ℕ), (QprimeFP.{u} r' BD.data κ M).obj (ι k))
        i ((single.{u+1 u+2} (Condensed.{u u+1 u+2} Ab.{u+1}) 0).obj V.to_Cond) j,
      rw ← iso.eq_inv_comp at this,
      rw ← reassoc_of this, refl },
    { simp only [category.assoc, nat_trans.naturality, ← nat_trans.comp_app_assoc,
        ← functor.map_comp_assoc, ← functor.map_comp, ← nat_trans.comp_app, ← op_comp],
      rw Tinv2_iso_of_bicartesian_aux_3,
      simp only [functor.map_comp, op_comp, nat_trans.comp_app, category.assoc],
      have := Ext_coproduct_iso_π _
        (λ (k : ulift.{u+1 0} ℕ), (QprimeFP.{u} r' BD.data κ M).obj (ι k))
        i ((single.{u+1 u+2} (Condensed.{u u+1 u+2} Ab.{u+1}) 0).obj V.to_Cond) j,
      rw ← iso.eq_inv_comp at this,
      rw ← reassoc_of this,
      refl,
      { apply homotopy_category.colimit_cofan_bdd } } },
  apply Tinv2_iso_of_bicartesian_aux_1,
end

lemma Tinv2_iso_of_bicartesian [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (hκ : Lbar.sufficiently_increasing κ ι hι)
  (hκ₂ : Lbar.sufficiently_increasing κ₂ ι hι)
  (i : ℤ)
  (H1 : (shift_sub_id.commsq (ExtQprime.Tinv2 r r' BD.data κ κ₂ M V i) ι hι).bicartesian)
  (H2 : (shift_sub_id.commsq (ExtQprime.Tinv2 r r' BD.data κ κ₂ M V (i+1)) ι hι).bicartesian) :
  is_iso (((Ext (i+1)).map ((BD.eval freeCond'.{u}).map M.Tinv_cond).op).app
    ((single (Condensed Ab) 0).obj V.to_Cond) -
    ((Ext (i+1)).obj ((BD.eval freeCond').op.obj (op (M.to_Condensed)))).map
      ((single (Condensed Ab) 0).map
        (Condensed.of_top_ab_map
          (normed_group_hom.to_add_monoid_hom normed_with_aut.T.inv) (normed_group_hom.continuous _)))) :=
begin
  let Vc := (single (Condensed Ab) 0).obj V.to_Cond,
  have SES₁ := QprimeFP.short_exact BD κ₂ M ι hι hκ₂,
  have SES₂ := QprimeFP.short_exact BD κ M ι hι hκ,
  have := Ext_iso_of_bicartesian_of_bicartesian SES₁ SES₂
    (sigma_map _ (QprimeFP_int.Tinv BD.data _ _ M))
    (sigma_map _ (QprimeFP_int.Tinv BD.data _ _ M))
    (category_theory.functor.map _ M.Tinv_cond)
    (sigma_map _ (QprimeFP_int.ι BD.data _ _ M))
    (sigma_map _ (QprimeFP_int.ι BD.data _ _ M))
    (commsq_shift_sub_id_Tinv BD.data _ _ M ι hι)
    (commsq_sigma_proj_Tinv BD _ _ M ι)
    (commsq_shift_sub_id_ι BD.data _ _ M ι hι)
    (commsq_sigma_proj_ι BD _ _ M ι)
    Vc ((single _ _).map $ Condensed.of_top_ab_map
      (normed_group_hom.to_add_monoid_hom normed_with_aut.T.inv) (normed_group_hom.continuous _))
    _
    (Tinv2_iso_of_bicartesian_aux _ _ _ _ _ _ _ _ _ H1)
    (Tinv2_iso_of_bicartesian_aux _ _ _ _ _ _ _ _ _ H2),
  delta Ext_Tinv2 at this,
  simpa only [op_id, category_theory.functor.map_id, category.id_comp, nat_trans.id_app],
end

lemma Tinv2_iso_of_bicartesian' [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (H : ∀ i, ∃ (ι) (hι),
    Lbar.sufficiently_increasing κ ι hι ∧
    Lbar.sufficiently_increasing κ₂ ι hι ∧
    (shift_sub_id.commsq (ExtQprime.Tinv2 r r' BD.data κ κ₂ M V i) ι hι).bicartesian ∧
    (shift_sub_id.commsq (ExtQprime.Tinv2 r r' BD.data κ κ₂ M V (i+1)) ι hι).bicartesian)
  (i : ℤ) :
  is_iso (((Ext i).map ((BD.eval freeCond'.{u}).map M.Tinv_cond).op).app
    ((single (Condensed Ab) 0).obj V.to_Cond) -
    ((Ext i).obj ((BD.eval freeCond').op.obj (op (M.to_Condensed)))).map
      ((single (Condensed Ab) 0).map
        (Condensed.of_top_ab_map
          (normed_group_hom.to_add_monoid_hom normed_with_aut.T.inv) (normed_group_hom.continuous _)))) :=
begin
  obtain ⟨i, rfl⟩ : ∃ k, k+1 = i := ⟨i-1, sub_add_cancel _ _⟩,
  obtain ⟨ι, hι, hκ, hκ₂, H1, H2⟩ := H i,
  apply Tinv2_iso_of_bicartesian _ _ _ _ _ _ ι hι hκ hκ₂ i H1 H2,
end

end preps
