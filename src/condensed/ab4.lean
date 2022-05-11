import for_mathlib.ab4
import condensed.extr.equivalence
import category_theory.limits.preserves.limits
import category_theory.adjunction.evaluation

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

instance : AB4 Ab.{u+1} := sorry

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
