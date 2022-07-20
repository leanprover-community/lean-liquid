import for_mathlib.derived.ext_coproducts
import for_mathlib.product_op

.

open category_theory
open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A] [has_coproducts A]

namespace homological_complex

noncomputable
def sigma_single_component {α : Type v} (i : ℤ) (X : α → A) :
  (∐ (λ a, (single A (complex_shape.up ℤ) i).obj (X a))).X i ≅ ∐ X :=
{ hom := (is_colimit_of_preserves (eval _ _ i) (colimit.is_colimit
      (discrete.functor $ λ a, (single A (complex_shape.up ℤ) i).obj (X a)))).desc ⟨∐ X,
    discrete.nat_trans $ λ a, eq_to_hom (if_pos rfl) ≫ sigma.ι _ a.as⟩,
  inv := sigma.desc $ λ a, eq_to_hom (if_pos rfl).symm ≫
    (sigma.ι (λ (a : α), (single A (complex_shape.up ℤ) i).obj (X a)) a).f i,
  hom_inv_id' := begin
    apply (is_colimit_of_preserves (eval A (complex_shape.up ℤ) i)
      (colimit.is_colimit (discrete.functor
        (λ (a : α), (single A (complex_shape.up ℤ) i).obj (X a))))).hom_ext,
    rintro ⟨j⟩,
    dsimp,
    rw category.comp_id,
    slice_lhs 1 2
    { erw (is_colimit_of_preserves (eval A (complex_shape.up ℤ) i)
        (colimit.is_colimit (discrete.functor
        (λ (a : α), (single A (complex_shape.up ℤ) i).obj (X a))))).fac },
    dsimp,
    rw [category.assoc, colimit.ι_desc], dsimp,
    simp only [eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp],
  end,
  inv_hom_id' := begin
    ext ⟨j⟩,
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, category.comp_id],
    erw (is_colimit_of_preserves (eval A (complex_shape.up ℤ) i)
      (colimit.is_colimit (discrete.functor (λ (a : α),
      (single A (complex_shape.up ℤ) i).obj (X a))))).fac,
    dsimp, simp only [eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp],
  end }

noncomputable
def sigma_single_component_of_eq {α : Type v} (j i : ℤ) (X : α → A) (h : j = i) :
  (∐ (λ a, (single A (complex_shape.up ℤ) i).obj (X a))).X j ≅ ∐ X :=
eq_to_iso (congr_arg _ h) ≪≫ sigma_single_component i X

noncomputable
def single_sigma_iso {α : Type v} (i : ℤ) (X : α → A) :
  (single A (complex_shape.up ℤ) i).obj (∐ X) ≅
  ∐ (λ a, (single A _ i).obj (X a)) :=
{ hom :=
  { f := λ j, if h : j = i then eq_to_hom (if_pos h) ≫
      sigma.desc (λ a, sigma.ι _ _ ≫ (sigma_single_component_of_eq j i X h).inv) else 0,
    comm' := begin
      rintro j k (rfl : _ = _),
      rcases eq_or_ne j i with (rfl|hij),
      { rw [dif_pos rfl, dif_neg], swap, { exact succ_ne_self j },
        simp only [category.assoc, single_obj_d, zero_comp, preadditive.is_iso.comp_left_eq_zero,
          sigma_single_component_of_eq, iso.trans_inv, sigma_single_component, eq_to_hom_refl,
          colimit.ι_desc_assoc, eq_to_iso, category.comp_id, cofan.mk_ι_app, colimit.ι_desc],
        ext, simp },
      { rw [dif_neg hij, zero_comp],
        split_ifs with hij',
        { subst i, simp only [single_obj_d, zero_comp], },
        { rw comp_zero } },
    end },
  inv := sigma.desc $ λ a,
  { f := λ j, if h : j = i then
      eq_to_hom (if_pos h) ≫
        sigma.ι _ _ ≫
        eq_to_hom (if_pos h).symm else 0,
    comm' := begin
      rintro j k (rfl : _ = _),
      rcases eq_or_ne j i with (rfl|hij),
      { rw [dif_pos rfl, dif_neg], swap, { exact succ_ne_self j },
        simp only [category.assoc, single_obj_d, zero_comp, comp_zero], },
      { rw [dif_neg hij, zero_comp],
        split_ifs with hij',
        { subst i, simp only [single_obj_d, zero_comp], },
        { rw comp_zero } },
    end },
  hom_inv_id' := begin
    ext j, dsimp,
    rcases eq_or_ne j i with (rfl|hij),
    { rw [dif_pos rfl],
      simp only [category.assoc],
      rw ← is_iso.eq_inv_comp (eq_to_hom _), swap, apply_instance,
      ext ⟨a⟩, simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc,
        inv_eq_to_hom, category.comp_id],
      dsimp [sigma_single_component_of_eq, sigma_single_component],
      simp only [category.comp_id, colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc],
      rw [← homological_complex.comp_f, colimit.ι_desc], dsimp,
      rw dif_pos rfl, simp only [eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp] },
    { rw [dif_neg hij, zero_comp, if_neg hij, eq_comm, ← is_zero_iff_id_eq_zero],
      exact limits.is_zero_zero A }
  end,
  inv_hom_id' := begin
    apply colimit.hom_ext, rintro ⟨j⟩,
    rw [colimit.ι_desc_assoc, cofan.mk_ι_app, category.comp_id],
    ext n,
    simp only [comp_f],
    rcases eq_or_ne n i with (rfl|hin),
    { rw [dif_pos rfl, dif_pos rfl],
      simp only [category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp,
        colimit.ι_desc, cofan.mk_ι_app, sigma_single_component_of_eq, iso.trans_inv,
        sigma_single_component, colimit.ι_desc_assoc, eq_to_iso, category.comp_id], },
    { rw [dif_neg hin, zero_comp], apply is_zero.eq_of_src,
      dsimp, rw if_neg hin, exact limits.is_zero_zero A }
  end }

noncomputable
instance preserves_coproducts_single {α : Type v} (i : ℤ) :
  preserves_colimits_of_shape (discrete α) (single A (complex_shape.up ℤ) i) :=
preserves_coproducts_aux _ (λ X, single_sigma_iso _ _) $ λ X a,
begin
  ext j,
  simp only [comp_f, single_map_f, single_sigma_iso],
  split_ifs with hj,
  { subst j,
    simp only [category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, eq_to_iso_refl,
      iso.trans_inv, iso.refl_inv, category.comp_id,
      sigma_single_component,
      category.id_comp, colimit.ι_desc, cofan.mk_ι_app, sigma_single_component_of_eq], },
  { apply is_zero.eq_of_tgt,
    apply is_zero.of_iso _ ((homological_complex.eval _ _ j).map_iso $ single_sigma_iso _ _).symm,
    dsimp, rw if_neg hj, apply limits.is_zero_zero }
end

end homological_complex

namespace homotopy_category

noncomputable
instance preserves_coproducts_single {α : Type v} (i : ℤ) :
  preserves_colimits_of_shape (discrete α) (single A i) :=
limits.comp_preserves_colimits_of_shape (homological_complex.single A (complex_shape.up ℤ) i)
  (quotient A (complex_shape.up ℤ))

end homotopy_category

namespace bounded_homotopy_category

instance uniformly_bounded_single {α : Type v} (i : ℤ) (X : α → A) :
  uniformly_bounded (λ a : α, (single A i).obj (X a)) :=
begin
  refine ⟨⟨i+1, λ a k hk, _⟩⟩,
  dsimp only [single, homotopy_category.single, functor.comp_obj, function.comp_app,
    homotopy_category.quotient_obj_as, homological_complex.single],
  rw if_neg,
  { exact is_zero_zero _ },
  { rintro rfl, linarith only [hk] }
end

instance has_coproduct_of_shape_single {α : Type v} (i : ℤ)
  (X : α → A) : has_coproduct (λ a, (single A i).obj (X a)) :=
bounded_homotopy_category.has_coproduct_of_uniform_bound _

noncomputable
def single_sigma_iso {α : Type v} (i : ℤ) (X : α → A) :
  (single A i).obj (∐ X) ≅ ∐ λ (a : α), (single A i).obj (X a) :=
let E : discrete.functor X ⋙ homotopy_category.single A i ≅
  discrete.functor (λ (a : α), (single A i).obj (X a)) ⋙ forget A :=
  discrete.nat_iso (λ a, iso.refl _) in
mk_iso $
preserves_colimit_iso (homotopy_category.single A i) (discrete.functor X) ≪≫
has_colimit.iso_of_nat_iso E ≪≫
(preserves_colimit_iso (forget A) $ discrete.functor (λ a, (single A i).obj (X a))).symm

noncomputable
instance preserves_coproducts_single {α : Type v}
  [has_coproducts A]
  (i : ℤ) :
  preserves_colimits_of_shape (discrete α) (single A i) :=
preserves_coproducts_aux _
(λ X, single_sigma_iso i X)
begin
  intros X a,
  let f : _ := _, show _ = f,
  apply (forget A).map_injective, rw [functor.map_comp],
  dsimp only [single_sigma_iso, forget, mk_iso, iso.trans_hom, iso.symm_hom, _root_.id, single],
  simp_rw [← category.assoc], rw [iso.comp_inv_eq],
  change _ = (forget A).map f ≫ _,
  erw ι_preserves_colimits_iso_hom,
  erw ι_preserves_colimits_iso_hom,
  rw has_colimit.iso_of_nat_iso_ι_hom,
  simp only [discrete.nat_iso_hom_app, iso.refl_hom, category.id_comp],
  refl,
end

variables [enough_projectives A]

instance Ab_op_has_colimits : has_colimits Abᵒᵖ := has_colimits_op_of_has_limits

noncomputable
instance preserves_coproducts_Ext' {α : Type v} (i : ℤ) (Y : A) [AB4 A] :
  preserves_colimits_of_shape (discrete α)
  ((Ext' i).flip.obj Y).right_op :=
preserves_coproducts_aux _
(λ X, begin
  let e₁ : (single A 0).obj (∐ X) ≅ ∐ _ := single_sigma_iso _ _,
  let e₂ : ((Ext i).obj (opposite.op ((single A 0).obj (∐ X)))).obj ((single A 0).obj Y) ≅
    ((Ext i).obj (opposite.op (∐ _))).obj ((single A 0).obj Y) :=
    ((Ext i).map_iso e₁.symm.op).app _,
  let e₃ : ((Ext i).obj (opposite.op (∐ λ (a : α), (single A 0).obj (X a)))).obj
    ((single A 0).obj Y) ≅ ∏ _ := Ext_coproduct_iso _ _ _,
  let e₄ : opposite.op (∏ λ (a : α), ((Ext i).obj (opposite.op ((single A 0).obj (X a)))).obj ((single A 0).obj Y)) ≅
    ∐ _ := op_product_iso _,
  refine (e₃.symm ≪≫ e₂.symm).op ≪≫ e₄,
end)
begin
  intros X a, dsimp only [iso.trans_hom, iso.symm_hom, iso.op_hom, Ext',
    op_comp, ← iso.op_inv],
  simp only [← category.assoc],
  rw [← iso.eq_comp_inv, iso.comp_inv_eq],
  dsimp only [op_product_iso],
  erw colimit.ι_desc,
  dsimp,
  simp_rw ← op_comp,
  rw ι_Ext_coproduct_iso',
  rw [← nat_trans.comp_app, ← functor.map_comp, ← op_comp],
  congr' 4,
  dsimp [single_sigma_iso], simp only [category.assoc],
  dsimp [preserves_colimit_iso, is_colimit.cocone_point_unique_up_to_iso],
  erw (preserves_colimit.preserves (colimit.is_colimit (discrete.functor X))).fac_assoc,
  erw colimit.ι_desc_assoc,
  dsimp, simpa,
end

end bounded_homotopy_category
