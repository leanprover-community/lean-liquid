import for_mathlib.ab4
import condensed.extr.equivalence
import category_theory.limits.preserves.limits
import category_theory.adjunction.evaluation
import algebra.group.ulift

.

universe u

open category_theory
open category_theory.limits

instance : has_colimits (ExtrSheafProd.{u} Ab.{u+1}) :=
has_colimits_of_has_colimits_creates_colimits
(Condensed_ExtrSheafProd_equiv _).inverse

instance : has_limits (ExtrSheafProd.{u} Ab.{u+1}) :=
has_limits_of_has_limits_creates_limits
(Condensed_ExtrSheafProd_equiv _).inverse

instance : has_colimits_of_size.{u} Ab.{u+1} :=
has_colimits_of_size_shrink.{u u (u+1) (u+1)} Ab.{u+1}

def Ab.pt {X : Ab.{u}} (x : X) :
  AddCommGroup.of (ulift.{u} ℤ) ⟶ X :=
{ to_fun := λ a, zmultiples_add_hom _ x a.down,
  map_zero' := by simp,
  map_add' := λ a b, by rw [ulift.add_down, add_monoid_hom.map_add] }

lemma Ab.pt_apply {X : Ab.{u}} (x : X) (n : ℤ) :
  Ab.pt x ⟨n⟩ = n • x := by { dsimp [Ab.pt], simp }

lemma AddCommGroup.injective_of_mono' {X Y : Ab.{u}} (f : X ⟶ Y) [mono f] :
  function.injective f :=
begin
  intros a b h,
  have : Ab.pt a ≫ f = Ab.pt b ≫ f,
  { ext ⟨n⟩, simp [Ab.pt_apply, f.map_zsmul, h], },
  rw cancel_mono at this,
  apply_fun (λ e, e ⟨1⟩) at this,
  simpa [Ab.pt_apply] using this,
end

open_locale classical

noncomputable
def Ab.cofan {α : Type (u+1)} (X : α → Ab.{u+1}) :
  cofan X :=
cofan.mk
(AddCommGroup.of $ Π₀ x, X x)
(λ a, dfinsupp.single_add_hom (λ x, X x) a)

noncomputable
def Ab.is_colimit_cofan {α : Type (u+1)} (X : α → Ab.{u+1}) :
  is_colimit (Ab.cofan X) :=
{ desc := λ S, dfinsupp.lift_add_hom
    (λ i, let e : X i ⟶ S.X := S.ι.app i in e),
  fac' := sorry,
  uniq' := sorry }

instance : AB4 Ab.{u+1} :=
begin
  constructor,
  introsI α X Y f hf,
  let t := _, change mono t,
  let eX : (∐ λ (a : α), X a) ≅ (Ab.cofan X).X :=
    (colimit.is_colimit _).cocone_point_unique_up_to_iso (Ab.is_colimit_cofan X),
  let eY : (∐ λ (a : α), Y a) ≅ (Ab.cofan Y).X :=
    (colimit.is_colimit _).cocone_point_unique_up_to_iso (Ab.is_colimit_cofan Y),
  let q : (Ab.cofan X).X ⟶ (Ab.cofan Y).X :=
    (Ab.is_colimit_cofan X).desc ⟨(Ab.cofan Y).X,
    λ a, f a ≫ (Ab.cofan Y).ι.app a, _⟩,
  swap, { sorry },
  haveI : mono q,
  { apply concrete_category.mono_of_injective,
    rintros (u v : Π₀ x, X x) h, ext w,
    dsimp [q, Ab.is_colimit_cofan, Ab.cofan] at h,
    apply_fun (λ e, (e : Π₀ w, Y w) w) at h,
    simp_rw dfinsupp.sum_add_hom_apply at h,
    apply_fun f w,
    swap, { sorry },
    let q : Π i, Y i → Π₀ i, Y i := dfinsupp.single,
    let qq : Π i, X i → Π₀ i, Y i := λ i, (q i) ∘ (f i),
    change u.sum (λ i, qq i) w = v.sum (λ i, qq i) w at h,
    rw @dfinsupp.sum_apply α (λ i, Y i) α _ (λ i, X i) _ _ _ u qq w at h,
    rw @dfinsupp.sum_apply α (λ i, Y i) α _ (λ i, X i) _ _ _ v qq w at h,
    simp only [dfinsupp.single_apply] at h,
    dsimp [dfinsupp.sum] at h,
    simp_rw [finset.sum_dite_eq'] at h,
    convert h,
    all_goals
    { split_ifs with hh hh, { refl },
      simp only [dfinsupp.mem_support_to_fun, not_not] at hh,
      simp only [hh, (f w).map_zero] } },
  suffices : t = eX.hom ≫ q ≫ eY.inv,
  { rw this, apply_instance },
  sorry
end

instance {C : Type (u+1)} [category.{u} C] : AB4 (C ⥤ Ab.{u+1}) :=
begin
  constructor,
  intros α X Y f hf,
  let t := _, change mono t,
  rw category_theory.nat_trans.mono_iff_app_mono,
  intros c,
  let eX : (∐ λ (a : α), X a).obj c ≅ (∐ λ (a : α), (X a).obj c) :=
    (is_colimit_of_preserves ((evaluation _ _).obj c)
      (colimit.is_colimit _)).cocone_point_unique_up_to_iso (colimit.is_colimit _)
    ≪≫ has_colimit.iso_of_nat_iso (discrete.nat_iso (λ _, iso.refl _)),
   let eY : (∐ λ (a : α), Y a).obj c ≅ (∐ λ (a : α), (Y a).obj c) :=
    (is_colimit_of_preserves ((evaluation _ _).obj c)
      (colimit.is_colimit _)).cocone_point_unique_up_to_iso (colimit.is_colimit _)
    ≪≫ has_colimit.iso_of_nat_iso (discrete.nat_iso (λ _, iso.refl _)),
  let tt : (∐ λ (a : α), (X a).obj c) ⟶ (∐ λ (a : α), (Y a).obj c) :=
    sigma.desc (λ a, (f a).app c ≫ sigma.ι _ a),
  haveI : mono tt,
  { dsimp [tt],
    apply AB4.cond, intros a, specialize hf a,
    rw category_theory.nat_trans.mono_iff_app_mono at hf,
    apply hf },
  suffices : t.app c = eX.hom ≫ tt ≫ eY.inv,
  { rw this, apply_instance },
  dsimp [eX, tt, t, eY],
  apply ((is_colimit_of_preserves ((evaluation _ _).obj c) (colimit.is_colimit _))).hom_ext,
  intros a,
  dsimp [is_colimit.cocone_point_unique_up_to_iso],
  simp only [category.assoc, ← nat_trans.comp_app, colimit.ι_desc],
  slice_rhs 0 1
  { erw ((is_colimit_of_preserves ((evaluation _ _).obj c) (colimit.is_colimit _))).fac },
  slice_rhs 0 1
  { erw colimit.ι_desc },
  dsimp,
  simp only [category.id_comp, colimit.ι_desc, cofan.mk_ι_app, category.assoc,
    has_colimit.iso_of_nat_iso_ι_inv, discrete.nat_iso_inv_app, functor.map_cocone_ι_app,
    colimit.cocone_ι, evaluation_obj_map],
  dsimp, simp, apply_instance
end

noncomputable
instance : creates_limits (ExtrSheafProd_to_presheaf.{u} Ab.{u+1}) :=
begin
  change creates_limits ((ExtrSheaf_ExtrSheafProd_equiv _).inverse ⋙
    Sheaf_to_presheaf _ _),
  apply_with category_theory.comp_creates_limits { instances := ff },
  apply_instance,
  exact @Sheaf.category_theory.Sheaf_to_presheaf.category_theory.creates_limits.{(u+2) u (u+1)}
    ExtrDisc.{u} _ ExtrDisc.proetale_topology Ab.{u+1} _ _,
end

instance : AB4 (ExtrSheafProd.{u} Ab.{u+1}) :=
AB4_of_preserves_colimits_of_reflects_limits_of_AB4
  (ExtrSheafProd_to_presheaf _)

-- TODO: Prove a lemma about transporting AB4 across an equivalence.
instance : AB4 (Condensed.{u} Ab.{u+1}) :=
AB4_of_preserves_colimits_of_reflects_limits_of_AB4
    (Condensed_ExtrSheafProd_equiv.{u} Ab.{u+1}).functor
