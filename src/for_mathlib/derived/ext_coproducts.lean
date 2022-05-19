import for_mathlib.derived.bounded_homotopy_category
import for_mathlib.is_quasi_iso_sigma
import for_mathlib.coprod_op
import for_mathlib.derived.example

open category_theory
open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A] [has_coproducts A]

open_locale zero_object

namespace bounded_homotopy_category

noncomputable
def cofan {α : Type v} (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] : cofan X := cofan.mk
{ val := (homotopy_category.colimit_cofan $ λ a : α, (X a).val).X,
  bdd := begin
    obtain ⟨n,hn⟩ := homotopy_category.is_uniformly_bounded_above.cond (val ∘ X),
      use n, intros i hi,
    dsimp [homotopy_category.colimit_cofan],
    let e : (∐ λ (a : α), (X a).val.as).X i ≅
      (∐ λ (a : α), (X a).val.as.X i) := homotopy_category.coproduct_iso _ _,
    refine is_zero_of_iso_of_zero _ e.symm,
    apply category_theory.is_zero_colimit,
    intros j,
    apply hn j _ hi,
  end }
(λ a, (homotopy_category.colimit_cofan _).ι.app a)

noncomputable
def is_colimit_cofan {α : Type v} (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] : is_colimit (cofan X) :=
{ desc := λ S, (homotopy_category.is_colimit_cofan
    (λ a : α, (X a).val)).desc ((forget A).map_cocone S),
  fac' := begin
    intros S j,
    erw (homotopy_category.is_colimit_cofan (λ a : α, (X a).val)).fac
      ((forget A).map_cocone S) j, refl,
  end,
  uniq' := begin
    intros S m hm,
    apply (homotopy_category.is_colimit_cofan (λ a : α, (X a).val)).hom_ext,
    intros j,
    specialize hm j,
    erw hm,
    erw (homotopy_category.is_colimit_cofan (λ a : α, (X a).val)).fac,
    refl,
  end }

instance has_coproduct_of_uniform_bound {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] :
  has_coproduct X :=
begin
  constructor, apply nonempty.intro,
  refine ⟨cofan X, is_colimit_cofan X⟩,
end

instance is_K_projective_sigma {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X]
  [∀ a, homotopy_category.is_K_projective (X a).val] :
  homotopy_category.is_K_projective (sigma_obj X).val :=
begin
  let e : (sigma_obj X) ≅ (cofan X).X :=
    (colimit.is_colimit _).cocone_point_unique_up_to_iso (is_colimit_cofan X),
  let ee := (forget A).map_iso e,
  suffices : homotopy_category.is_K_projective ((forget A).obj (cofan X).X),
  { resetI, apply homotopy_category.is_K_projective_of_iso _ _ ee.symm },
  dsimp [forget, cofan],
  apply_instance,
end

noncomputable
instance forget_preserves_coproduct {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] :
  preserves_colimit (discrete.functor X) (forget A) :=
begin
  apply preserves_colimit_of_preserves_colimit_cocone (is_colimit_cofan X),
  let E : (forget A).map_cocone (cofan X) ≅
    homotopy_category.colimit_cofan (val ∘ X) :=
    cocones.ext (iso.refl _) _,
  rotate,
  { intros a, dsimp [forget, cofan], simpa only [category.comp_id] },
  apply is_colimit.of_iso_colimit _ E.symm,
  apply homotopy_category.is_colimit_cofan,
end

lemma is_quasi_iso_sigma
  [AB4 A]
  {α : Type v}
  (X P : α → bounded_homotopy_category A)
  [uniformly_bounded X]
  [uniformly_bounded P]
  (π : Π a, P a ⟶ X a)
  [∀ a, homotopy_category.is_quasi_iso (π a)] :
  homotopy_category.is_quasi_iso
    (sigma.desc $ λ a : α, π a ≫ sigma.ι X a : sigma_obj P ⟶ sigma_obj X) :=
begin
  let t := sigma.desc (λ (a : α), π a ≫ sigma.ι X a),
  change homotopy_category.is_quasi_iso ((forget A).map t),
  let eP : (forget A).obj (∐ P) ≅ ∐ (λ a, (forget A).obj (P a)) :=
    preserves_colimit_iso (forget A) _,
  let eX : (forget A).obj (∐ X) ≅ ∐ (λ a, (forget A).obj (X a)) :=
    preserves_colimit_iso (forget A) _,
  let s : ∐ (λ a, (forget A).obj (P a)) ⟶ ∐ (λ a, (forget A).obj (X a)) :=
    sigma.desc (λ (a : α), π a ≫ sigma.ι (val ∘ X) a),
  suffices : (forget A).map t = eP.hom ≫ s ≫ eX.inv,
  { rw this,
    apply homotopy_category.is_quasi_iso_comp },
  apply (is_colimit_of_preserves (forget A) (colimit.is_colimit _)).hom_ext,
  swap, apply_instance,
  intros a,
  dsimp [t, s, eP, eX, preserves_colimit_iso, is_colimit.cocone_point_unique_up_to_iso],
  rw [← (forget A).map_comp, colimit.ι_desc],
  slice_rhs 0 1
  { erw (is_colimit_of_preserves (forget A) (colimit.is_colimit (discrete.functor P))).fac },
  erw colimit.ι_desc,
  dsimp, simp only [category.assoc], erw colimit.ι_desc,
  dsimp, simp only [functor.map_comp], refl,
end

variables [enough_projectives A]

noncomputable
def uniform_π {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] : sigma_obj (replace_uniformly X) ⟶ sigma_obj X :=
sigma.desc $ λ a, π_uniformly _ _ ≫ sigma.ι _ a

instance is_quasi_iso_sigma_map_π_uniformly
  [AB4 A]
  {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X] :
  homotopy_category.is_quasi_iso (uniform_π X) :=
is_quasi_iso_sigma _ _ _

open opposite

noncomputable
def Ext_coproduct_iso
  [AB4 A]
  {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X]
  (i : ℤ) (Y) :
  ((Ext i).obj (op (sigma_obj X))).obj Y ≅
  pi_obj (λ a : α, ((Ext i).obj (op (X a))).obj Y) :=
Ext_iso i _ _ _ (uniform_π X) ≪≫
category_theory.preadditive_yoneda_coproduct_iso (replace_uniformly X) (Y⟦i⟧) ≪≫
category_theory.pi_iso _ _ (λ a, (Ext_iso i _ _ _ (π_uniformly X a)).symm)

lemma Ext_coproduct_iso_naturality
  [AB4 A]
  {α : Type v}
  (X₁ X₂ : α → bounded_homotopy_category A)
  [uniformly_bounded X₁]
  [uniformly_bounded X₂]
  (g : X₁ ⟶ X₂)
  (i : ℤ) (Y) :
  ((Ext i).map (sigma.desc (λ b, g b ≫ sigma.ι X₂ b) : ∐ X₁ ⟶ ∐ X₂).op).app Y ≫
  (Ext_coproduct_iso _ _ _).hom =
  (Ext_coproduct_iso _ _ _).hom ≫
  pi.lift (λ b, pi.π _ b ≫ ((Ext i).map (g b).op).app Y) :=
begin
  dsimp only [Ext_coproduct_iso, Ext, Ext0, Ext_iso, functor.comp_map, whiskering_left,
    whisker_left, iso.trans_hom, functor.map_iso, preadditive_yoneda_coproduct_iso,
    functor.flip, pi_iso, as_iso, preadditive_yoneda_coproduct_to_product],
  simp only [category.assoc],
  simp only [quiver.hom.unop_op, iso.op_hom, replacement_iso_hom, iso.op_inv,
    replacement_iso_inv, iso.symm_mk],
  apply limit.hom_ext,
  intros j,
  simp only [category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π_assoc],
  simp only [← functor.map_comp, ← op_comp],
  congr' 2,
  simp only [category.assoc],
  apply lift_ext (∐ X₂).π, swap, apply_instance,
  dsimp [quiver.hom.unop_op],
  simp only [category.assoc, lift_lifts, lift_lifts_assoc],
  dsimp [uniform_π],
  simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, colimit.ι_desc,
    lift_lifts_assoc],
end

lemma Ext_coproduct_iso_naturality'
  [AB4 A]
  {α : Type v}
  (X : α → bounded_homotopy_category A)
  [uniformly_bounded X]
  (i : ℤ) (Y₁ Y₂) (f : Y₁ ⟶ Y₂) :
  ((Ext i).obj (op (sigma_obj X))).map f ≫
  (Ext_coproduct_iso _ _ _).hom =
  (Ext_coproduct_iso _ _ _).hom ≫
  pi.lift (λ a, pi.π _ a ≫ ((Ext i).obj _).map f) :=
begin
  dsimp only [Ext_coproduct_iso, Ext, Ext0, Ext_iso, functor.comp_map, whiskering_left,
    whisker_left, iso.trans_hom, functor.map_iso, preadditive_yoneda_coproduct_iso,
    functor.flip, pi_iso, as_iso, preadditive_yoneda_coproduct_to_product,
    functor.comp_map, functor.comp_obj],
  simp only [category.assoc],
  simp only [quiver.hom.unop_op, iso.op_hom, replacement_iso_hom, iso.op_inv,
    replacement_iso_inv, iso.symm_mk],
  apply limit.hom_ext,
  intros j,
  simp only [category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π_assoc],
  erw nat_trans.naturality,
  erw nat_trans.naturality_assoc,
  erw nat_trans.naturality_assoc,
  refl,
end

end bounded_homotopy_category
