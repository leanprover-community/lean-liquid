import condensed.ab
import condensed.short_exact
import for_mathlib.AddCommGroup.direct_sum_colimit

import for_mathlib.AddCommGroup.explicit_products

open_locale classical big_operators

open category_theory
open category_theory.limits
open opposite

namespace Condensed

universes u
variables (F : as_small.{u+1} ℕ ⥤ Condensed.{u} Ab.{u+1})

noncomputable theory

def coproduct_to_colimit : (∐ F.obj) ⟶ colimit F :=
sigma.desc (λ i, colimit.ι _ i)

def coproduct_to_coproduct :
  (∐ F.obj) ⟶ (∐ F.obj)  :=
sigma.desc $ λ i,
  F.map (as_small.up.map $ hom_of_le $ nat.le_succ _) ≫
  sigma.ι _ (as_small.up.obj (as_small.down.obj i + 1))

def sigma_eval_iso {α : Type (u+1)} (X : α → Condensed.{u} Ab.{u+1})
  (S : ExtrDisc.{u}) :
  (∐ X).val.obj (op S.val) ≅ ∐ (λ a, (X a).val.obj (op S.val)) :=
preserves_colimit_iso (Condensed.evaluation _ S.val) _ ≪≫
has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ i, iso.refl _)

@[reassoc]
lemma ι_sigma_eval_iso {α : Type (u+1)} (X : α → Condensed.{u} Ab.{u+1})
  (S : ExtrDisc.{u}) (i : α) :
  (sigma.ι X i : X i ⟶ _).val.app (op S.val) ≫
  (sigma_eval_iso X S).hom = sigma.ι _ i :=
begin
  dsimp only [sigma_eval_iso],
  erw (is_colimit_of_preserves (Condensed.evaluation _ S.val) _).fac_assoc,
  erw colimit.ι_desc, dsimp, simp,
end

def sigma_eval_iso_direct_sum
  {α : Type (u+1)} (X : α → Condensed.{u} Ab.{u+1})
  (S : ExtrDisc.{u}) :
  (∐ X).val.obj (op S.val) ≅
  AddCommGroup.of (direct_sum α $ λ i, (X i).val.obj (op S.val)) :=
let φ : α → AddCommGroup.{u+1} := λ i, (X i).val.obj (op S.val) in
sigma_eval_iso _ _ ≪≫
(colimit.is_colimit (discrete.functor φ)).cocone_point_unique_up_to_iso
  (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1} φ)

def shift_cofan (S : ExtrDisc.{u}) (T : cofan (λ i, (F.obj i).val.obj (op S.val))) :
  cofan (λ i, (F.obj i).val.obj (op S.val)) :=
cofan.mk T.X $ λ (i : as_small.{u+1} ℕ),
begin
  refine _ ≫ T.ι.app (as_small.up.obj $ as_small.down.obj i + 1),
  refine (F.map _).val.app _,
  refine as_small.up.map _,
  refine hom_of_le _,
  exact nat.le_succ _,
end

def direct_sum_to_direct_sum (S : ExtrDisc.{u}) :
  AddCommGroup.of (direct_sum (as_small.{u+1} ℕ) (λ i, (F.obj i).val.obj (op S.val))) ⟶
  AddCommGroup.of (direct_sum (as_small.{u+1} ℕ) (λ i, (F.obj i).val.obj (op S.val))) :=
let φ : as_small.{u+1} ℕ → AddCommGroup := λ i, (F.obj i).val.obj (op S.val) in
(AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1} φ).desc
  (shift_cofan F S $ AddCommGroup.direct_sum_cofan.{u+1 u+1} φ)

def direct_sum_to_explicit_colimit (S : ExtrDisc.{u}) :
  AddCommGroup.of (direct_sum (as_small.{u+1} ℕ) (λ i, (F.obj i).val.obj (op S.val))) ⟶
  (AddCommGroup.explicit_cocone (F ⋙ Condensed.evaluation _ S.val)).X :=
(AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1} (λ i, (F.obj i).val.obj (op S.val))).desc
(cofan.mk (AddCommGroup.explicit_cocone (F ⋙ Condensed.evaluation _ S.val)).X $
  λ i, (AddCommGroup.explicit_cocone.{u+1}
  (F ⋙ Condensed.evaluation _ S.val)).ι.app i)

lemma key_lemma_aux (S : ExtrDisc.{u}) :
  direct_sum_to_explicit_colimit F S = quotient_add_group.mk' _ :=
begin
  apply (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1}
      (λ i, (F.obj i).val.obj (op S.val))).hom_ext, intros j,
  erw (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1}
      (λ i, (F.obj i).val.obj (op S.val))).fac, ext t,
  refl,
end

lemma key_lemma (S : ExtrDisc.{u}) :
  exact (direct_sum_to_direct_sum F S - 𝟙 _) (direct_sum_to_explicit_colimit F S) :=
begin
  rw AddCommGroup.exact_iff', split,
  { apply (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1}
      (λ i, (F.obj i).val.obj (op S.val))).hom_ext,
    intros j,
    simp only [preadditive.sub_comp, category.id_comp, preadditive.comp_sub, comp_zero],
    rw sub_eq_zero,
    dsimp [direct_sum_to_direct_sum, direct_sum_to_explicit_colimit],
    rw (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1}
      (λ i, (F.obj i).val.obj (op S.val))).fac_assoc,
    rw (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1}
      (λ i, (F.obj i).val.obj (op S.val))).fac,
    dsimp [shift_cofan], simp only [category.assoc],
    rw (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1}
      (λ i, (F.obj i).val.obj (op S.val))).fac,
    dsimp,
    apply (AddCommGroup.explicit_cocone (F ⋙ evaluation Ab S.val)).w },
  { rintros x hx, rw add_monoid_hom.mem_ker at hx, rw key_lemma_aux at hx,
    dsimp at hx,
    rw quotient_add_group.eq_zero_iff at hx,
    rw AddCommGroup.explicit_cocone_point_kernel_eq_of_as_small_nat at hx,
    apply add_subgroup.closure_induction hx,
    { rintros x ⟨i,t,rfl⟩, let tt := (AddCommGroup.direct_sum_cofan.{u+1 u+1}
        (λ j, (F.obj j).val.obj (op S.val))).ι.app i t,
      use tt,
      change _ - _ = _ - _, congr' 1,
      swap,
      { dsimp only [tt], rw id_apply,
        dsimp [AddCommGroup.direct_sum_cofan, AddCommGroup.direct_sum_ι],
        congr },
      { dsimp [tt], rw ← comp_apply,
        erw (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1}
          (λ j, (F.obj j).val.obj (op S.val))).fac,
        dsimp [shift_cofan, AddCommGroup.direct_sum_cofan, AddCommGroup.direct_sum_ι,
          AddCommGroup.to_as_small_succ],
        rw comp_apply,
        dsimp [AddCommGroup.as_small_succ],
        congr } },
    { use 0, simp only [map_zero], },
    { rintros x y ⟨x,rfl⟩ ⟨y,rfl⟩, use x + y, simp only [map_add], },
    { rintros x ⟨x,rfl⟩, use -x, simp only [map_neg], } },
end

lemma sigma_eval_iso_direct_sum_direct_sum_to_direct_sum (S : ExtrDisc.{u}) :
  (sigma_eval_iso_direct_sum F.obj S).hom ≫ direct_sum_to_direct_sum F S =
  (coproduct_to_coproduct _).val.app _ ≫ (sigma_eval_iso_direct_sum F.obj S).hom :=
begin
  apply (is_colimit_of_preserves (Condensed.evaluation Ab.{u+1} S.val)
    (colimit.is_colimit (discrete.functor F.obj))).hom_ext, intros j,
  dsimp [coproduct_to_coproduct],
  slice_rhs 1 2
  { rw [← nat_trans.comp_app, ← Sheaf.hom.comp_val, colimit.ι_desc], },
  dsimp [sigma_eval_iso_direct_sum, sigma_eval_iso], simp only [category.assoc],
  slice_lhs 1 2
  { erw (is_colimit_of_preserves (Condensed.evaluation Ab.{u+1} S.val)
    (colimit.is_colimit (discrete.functor F.obj))).fac },
  slice_rhs 2 3
  { erw (is_colimit_of_preserves (Condensed.evaluation Ab.{u+1} S.val)
    (colimit.is_colimit (discrete.functor F.obj))).fac },
  dsimp,
  simp only [has_colimit.iso_of_nat_iso_ι_hom, discrete.nat_iso_hom_app, category.assoc,
    colimit.comp_cocone_point_unique_up_to_iso_hom], dsimp,
  simp only [category.id_comp],
  erw (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1} (λ i, (F.obj i).val.obj (op S.val))).fac,
  refl,
end

def colimit_val_app_iso_explicit_colimit (S : ExtrDisc.{u}) :
  (colimit F).val.obj (op S.val) ≅
  (AddCommGroup.explicit_cocone (F ⋙ Condensed.evaluation _ S.val)).X :=
(is_colimit_of_preserves (Condensed.evaluation _ S.val)
  (colimit.is_colimit F)).cocone_point_unique_up_to_iso
  (AddCommGroup.is_colimit_explicit_cocone _)

lemma sigma_eval_iso_direct_sum_to_explicit_colimit (S : ExtrDisc.{u}) :
  (sigma_eval_iso_direct_sum F.obj S).hom ≫ direct_sum_to_explicit_colimit F S =
  (coproduct_to_colimit _).val.app _ ≫ (colimit_val_app_iso_explicit_colimit _ _).hom :=
begin
  apply (is_colimit_of_preserves (Condensed.evaluation Ab.{u+1} S.val)
    (colimit.is_colimit (discrete.functor F.obj))).hom_ext, intros j,
  dsimp [sigma_eval_iso_direct_sum, sigma_eval_iso, coproduct_to_colimit,
    colimit_val_app_iso_explicit_colimit],
  simp only [category.assoc],

  erw (is_colimit_of_preserves (Condensed.evaluation Ab.{u+1} S.val)
    (colimit.is_colimit (discrete.functor F.obj))).fac_assoc,
  slice_rhs 1 2
  { rw [← nat_trans.comp_app, ← Sheaf.hom.comp_val, colimit.ι_desc], },

  erw colimit.ι_desc_assoc,
  dsimp,
  simp only [category.id_comp, colimit.comp_cocone_point_unique_up_to_iso_hom_assoc],

  dsimp [direct_sum_to_explicit_colimit],
  erw
    (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1} (λ (i : as_small ℕ),
      (F.obj i).val.obj (op S.val))).fac,

  erw (is_colimit_of_preserves (evaluation Ab S.val) (colimit.is_colimit F)).fac,

  refl,
end

lemma ι_sigma_eval_iso_direct_sum {α : Type (u+1)} (X : α → Condensed.{u} Ab.{u+1})
  (S : ExtrDisc.{u}) (i : α) :
  (sigma.ι X i : X i ⟶ _).val.app (op S.val) ≫ (sigma_eval_iso_direct_sum X S).hom =
  direct_sum.of _ i :=
begin
  dsimp only [sigma_eval_iso_direct_sum],
  erw ι_sigma_eval_iso_assoc, erw colimit.ι_desc, refl,
end

instance epi_coproduct_to_colimit :
  epi (coproduct_to_colimit F) :=
begin
  constructor,
  intros Z a b h,
  apply colimit.hom_ext,
  intros j,
  apply_fun (λ e, sigma.ι F.obj j ≫ e) at h,
  dsimp [coproduct_to_colimit] at h,
  simpa using h,
end

instance mono_coproduct_to_coproduct :
  mono (coproduct_to_coproduct F - 𝟙 _) :=
begin
  rw mono_iff_ExtrDisc, intros S,
  let φ : as_small.{u+1} ℕ → AddCommGroup := λ i, (F.obj i).val.obj (op S.val),
  let e : (∐ F.obj).val.obj (ExtrDisc_to_Profinite.op.obj (op S)) ≅
    AddCommGroup.of (direct_sum (as_small.{u+1} ℕ) (λ i, φ i)) := sigma_eval_iso_direct_sum _ _,
  change mono (_ - _), dsimp,
  let D := AddCommGroup.direct_sum_cofan.{u+1 u+1} φ,
  let hD : is_colimit D := AddCommGroup.is_colimit_direct_sum_cofan _,
  let D' : cofan φ := cofan.mk D.X
    (λ i, _ ≫ D.ι.app (as_small.up.obj (as_small.down.obj i + 1))),
  swap,
  { refine (F.map _).val.app _,
    refine as_small.up.map _,
    refine hom_of_le _,
    exact nat.le_succ _ },
  let t : D.X ⟶ D'.X := (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1} φ).desc D',
  have ht : (coproduct_to_coproduct F).val.app (op S.val) = e.hom ≫ t ≫ e.inv,
  { rw [← category.assoc, iso.eq_comp_inv],
    apply (is_colimit_of_preserves (Condensed.evaluation Ab.{u+1} S.val)
      (colimit.is_colimit _)).hom_ext, intros j, swap, apply_instance,
    dsimp [coproduct_to_coproduct],
    rw [← category.assoc, ← nat_trans.comp_app, ← Sheaf.hom.comp_val, colimit.ι_desc],
    dsimp, rw category.assoc,
    erw ι_sigma_eval_iso_direct_sum,
    rw ← category.assoc,
    erw ι_sigma_eval_iso_direct_sum,
    erw hD.fac, refl },
  rw ht,
  have : 𝟙 ((∐ F.obj).val.obj (op S.val)) = e.hom ≫ 𝟙 _ ≫ e.inv, by simp,
  rw this,
  simp only [← preadditive.comp_sub, ← preadditive.sub_comp],
  suffices : mono (t - 𝟙 (AddCommGroup.of (direct_sum (as_small ℕ) (λ (i : as_small ℕ), ↥(φ i))))),
  { apply_with mono_comp { instances := ff }, apply_instance,
    apply_with mono_comp { instances := ff }, exact this, apply_instance },
  rw [AddCommGroup.mono_iff_injective, injective_iff_map_eq_zero],
  intros x hx,
  erw [sub_eq_zero, id_apply] at hx,
  ext ⟨i⟩,
  induction i with i IH,
  { rw ← hx,
    dsimp [t, AddCommGroup.is_colimit_direct_sum_cofan,
      AddCommGroup.direct_sum_desc, discrete.nat_trans, direct_sum.to_add_monoid],
    rw [dfinsupp.sum_add_hom_apply, dfinsupp.sum_apply],
    apply finset.sum_eq_zero,
    rintro ⟨j⟩ -,
    convert dif_neg _,
    rw [finset.mem_singleton],
    intro H, rw ulift.ext_iff at H, revert H, apply nat.no_confusion },
  { rw ← hx,
    dsimp [t, AddCommGroup.is_colimit_direct_sum_cofan,
      AddCommGroup.direct_sum_desc, discrete.nat_trans, direct_sum.to_add_monoid],
    rw [dfinsupp.sum_add_hom_apply, dfinsupp.sum_apply],
    rw dfinsupp.zero_apply at IH,
    convert finset.sum_eq_single (ulift.up $ i) _ _,
    { rw [IH, add_monoid_hom.map_zero, dfinsupp.zero_apply], },
    { rintro ⟨j⟩ - hj, convert dif_neg _, rw [finset.mem_singleton],
      intro H, apply hj, rw ulift.ext_iff at H ⊢, change i+1 = j+1 at H,
      change j = i, linarith only [H] },
    { intro, rw [IH, add_monoid_hom.map_zero, dfinsupp.zero_apply], } },
  recover, all_goals { apply_instance }
end

.

theorem exactness_in_the_middle_part_one :
  (coproduct_to_coproduct F - 𝟙 _) ≫ (coproduct_to_colimit F) = 0 :=
begin
  apply colimit.hom_ext, intros j,
  dsimp [coproduct_to_coproduct, coproduct_to_colimit],
  simp only [preadditive.comp_sub, preadditive.sub_comp, colimit.ι_desc_assoc,
    category.id_comp, category.comp_id, colimit.ι_desc],
  dsimp, simp,
end

theorem exactness_in_the_middle :
  exact (coproduct_to_coproduct F - 𝟙 _) (coproduct_to_colimit F) :=
begin
  rw exact_iff_ExtrDisc, intros S,
  let e₁ : (∐ F.obj).val.obj (ExtrDisc_to_Profinite.op.obj (op S)) ≅
    _ := sigma_eval_iso_direct_sum F.obj S,
  let e₂ : (colimit F).val.obj (op S.val) ≅ _ :=
    colimit_val_app_iso_explicit_colimit F S,
  let a := _, let b := _, change exact a b,
  have ha : a = e₁.hom ≫ (direct_sum_to_direct_sum _ _ - 𝟙 _) ≫ e₁.inv,
  { simp only [preadditive.sub_comp, category.id_comp, preadditive.comp_sub, iso.hom_inv_id],
    rw ← category.assoc,
    erw [sigma_eval_iso_direct_sum_direct_sum_to_direct_sum],
    simp only [category.assoc, iso.hom_inv_id, category.comp_id],
    refl },
  have hb : b = e₁.hom ≫ direct_sum_to_explicit_colimit _ _ ≫ e₂.inv,
  { dsimp [e₁, e₂],
    rw [← category.assoc, sigma_eval_iso_direct_sum_to_explicit_colimit],
    simp only [category.assoc, iso.hom_inv_id, category.comp_id],
    refl },
  rw [ha, hb], clear ha hb a b,
  suffices : exact (direct_sum_to_direct_sum F S - 𝟙 _) (direct_sum_to_explicit_colimit _ _),
  { rw ← category.assoc, apply exact_comp_inv_hom_comp,
    rw exact_iso_comp, rw exact_comp_iso, exact this },
  apply key_lemma,
end

theorem short_exact :
  short_exact (coproduct_to_coproduct F - 𝟙 _) (coproduct_to_colimit F) :=
begin
  constructor,
  apply exactness_in_the_middle,
end

end Condensed
