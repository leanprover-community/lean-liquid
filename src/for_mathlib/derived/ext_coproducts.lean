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

-- TODO: find better names... And move this stuff!

instance chain_complex_embed_cofan_uniformly_bounded
  {α : Type v}
  (X : α → chain_complex A ℕ) :
  bounded_homotopy_category.uniformly_bounded
  (λ a, chain_complex.to_bounded_homotopy_category.obj (X a)) :=
begin
  constructor, use 1, intros a i hi,
  rcases i with (_|i)|_,
  { exfalso, revert hi, dec_trivial },
  { exact is_zero_zero _, },
  { exfalso, revert hi, dec_trivial }
end

universe u'

def whisker_discrete_functor {α : Type v}
  {C : Type u} {D : Type u'} [category.{v} C] [category.{v} D] (F : C ⥤ D)
  (X : α → C) : discrete.functor X ⋙ F ≅ discrete.functor (F.obj ∘ X) :=
  discrete.nat_iso (λ i, iso.refl _)

noncomputable
lemma preserves_coproducts_aux
  {α : Type v} {C : Type u} {D : Type u'}
  [category.{v} C] [category.{v} D]
  (F : C ⥤ D)
  [has_coproducts_of_shape α C]
  [has_coproducts_of_shape α D]
  (e : Π (X : α → C), F.obj (∐ X) ≅ ∐ (λ a, F.obj (X a)))
  (he : ∀ (X : α → C) (a : α), F.map (sigma.ι X a) ≫ (e X).hom = sigma.ι _ a) :
  preserves_colimits_of_shape (discrete α) F :=
begin
  constructor, intros K,
  let E : K ≅ discrete.functor K.obj := discrete.nat_iso (λ _, iso.refl _),
  apply preserves_colimit_of_iso_diagram _ E.symm,
  apply preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit _),
  swap, apply_instance,
  let P := _, change is_colimit P,
  let P' := (cocones.precompose (whisker_discrete_functor F K.obj).inv).obj P,
  suffices : is_colimit P',
  { exact is_colimit.precompose_inv_equiv _ _ this },
  apply is_colimit.of_iso_colimit (colimit.is_colimit _), swap,
  change has_colimit (discrete.functor (λ a : α, F.obj (K.obj a))),
  apply_instance,
  symmetry,
  fapply cocones.ext,
  apply e,
  intros a,
  convert (he (λ b, (K.obj b))) a,
  dsimp [P', whisker_discrete_functor],
  rw category.id_comp,
end

noncomputable
instance homological_complex_embed_preserves_coproducts {α : Type v}
  {M N : Type} (c₁ : complex_shape M) (c₂ : complex_shape N) (e : c₁.embedding c₂) :
  preserves_colimits_of_shape (discrete α)
  (homological_complex.embed e : homological_complex A _ ⥤ _) :=
preserves_coproducts_aux
(homological_complex.embed e : homological_complex A _ ⥤ _)
(λ (X : α → homological_complex A c₁), homological_complex.hom.iso_of_components
(λ i,
begin
  rcases h : e.r i with _ | j,
  { refine homological_complex.embed.X_iso_of_none _ h ≪≫ _,
    refine _ ≪≫ (preserves_colimit_iso (homological_complex.eval A c₂ i) _).symm,
    refine (is_zero.iso_zero _).symm,
    apply is_zero_colimit,
    intros a,
    dsimp,
    exact homological_complex.embed.X_is_zero_of_none _ h },
  { refine homological_complex.embed.X_iso_of_some _ h ≪≫ _,
    refine (preserves_colimit_iso (homological_complex.eval _ _ _) _) ≪≫ _,
    refine _ ≪≫ (preserves_colimit_iso (homological_complex.eval _ _ _) _).symm,
    refine has_colimit.iso_of_nat_iso _,
    refine discrete.nat_iso _,
    intros b,
    dsimp,
    refine (homological_complex.embed.X_iso_of_some _ h).symm }
end) begin
  intros i j h,
  rcases h₁ : e.r i with _ | i';
  rcases h₂ : e.r j with _ | j',
  { apply is_zero.eq_of_src,
    apply homological_complex.embed.X_is_zero_of_none,
    assumption },
  { apply is_zero.eq_of_src,
    apply homological_complex.embed.X_is_zero_of_none,
    assumption },
  { apply is_zero.eq_of_tgt,
    refine is_zero.of_iso _
      (preserves_colimit_iso (homological_complex.eval _ _ _) _),
    apply is_zero_colimit, intros b,
    apply homological_complex.embed.X_is_zero_of_none,
    assumption },
  { simp_rw [h₁, h₂], dsimp,
    simp only [category.assoc],
    rw ← iso.eq_inv_comp,
    dsimp [homological_complex.embed, homological_complex.embed.obj],
    rw homological_complex.embed.d_of_some_of_some (∐ X) h₁ h₂,
    simp only [category.assoc, iso.inv_hom_id_assoc],
    apply (is_colimit_of_preserves (homological_complex.eval A c₁ i') _).hom_ext,
    intros a,
    simp only [functor.map_cocone_ι_app, colimit.cocone_ι, homological_complex.eval_map],
    slice_lhs 1 2 {
      erw (is_colimit_of_preserves (homological_complex.eval A c₁ i') _).fac },
    dsimp,
    simp only [has_colimit.iso_of_nat_iso_ι_hom, discrete.nat_iso_hom_app, iso.symm_hom,
      category.assoc, ι_preserves_colimits_iso_inv, homological_complex.eval_map,
      homological_complex.hom.comm, homological_complex.hom.comm_assoc],
    dsimp,
    rw iso.inv_comp_eq,
    slice_rhs 3 4
    { erw (is_colimit_of_preserves (homological_complex.eval A c₁ j') _).fac },
    dsimp,
    simp only [has_colimit.iso_of_nat_iso_ι_hom, discrete.nat_iso_hom_app, iso.symm_hom,
      category.assoc, ι_preserves_colimits_iso_inv, homological_complex.eval_map],
    slice_rhs 1 3
    { rw ← homological_complex.embed.d_of_some_of_some (X a) h₁ h₂ },
    apply colimit.is_colimit,
    apply_instance, }
    -- still annoying
  end)
sorry

noncomputable
def embed_coproduct_iso
  {α : Type v}
  (X : α → chain_complex A ℕ) :
  (homological_complex.embed complex_shape.embedding.nat_down_int_up).obj (∐ X) ≅
  (∐ λ (a : α), (homological_complex.embed complex_shape.embedding.nat_down_int_up).obj (X a)) :=
preserves_colimit_iso (homological_complex.embed complex_shape.embedding.nat_down_int_up) _ ≪≫
has_colimit.iso_of_nat_iso (whisker_discrete_functor _ _)

noncomputable
def chain_complex_embed_cofan_iso
  {α : Type v}
  (X : α → chain_complex A ℕ) :
  (bounded_homotopy_category.cofan
    (λ a, chain_complex.to_bounded_homotopy_category.obj (X a))) ≅
    ((cocones.precompose (whisker_discrete_functor _ X).inv).obj
    (chain_complex.to_bounded_homotopy_category.map_cocone
      (colimit.cocone (discrete.functor X)))) :=
cocones.ext
(bounded_homotopy_category.mk_iso $
  (homotopy_category.quotient _ _).map_iso $ (embed_coproduct_iso X).symm)
begin
  intros a,
  dsimp [bounded_homotopy_category.cofan,
    homotopy_category.colimit_cofan, whisker_discrete_functor],
  erw [category.id_comp, ← functor.map_comp],
  congr' 1,
  dsimp [embed_coproduct_iso],
  simp only [category.assoc],
  erw colimit.ι_desc_assoc,
  rw iso.comp_inv_eq,
  erw (is_colimit_of_preserves
    (homological_complex.embed complex_shape.embedding.nat_down_int_up) _).fac,
  dsimp [whisker_discrete_functor],
  rw category.id_comp,
end

noncomputable
instance chain_complex_to_bounded_homotopy_category_preserves_coproducts
  {α : Type v} :
  preserves_colimits_of_shape (discrete α)
  (chain_complex.to_bounded_homotopy_category : chain_complex A _ ⥤ _) :=
begin
  constructor, intros K,
  let E : K ≅ discrete.functor K.obj := discrete.nat_iso (λ _, iso.refl _),
  apply preserves_colimit_of_iso_diagram _ E.symm,
  apply preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit _),
  let Q : α → bounded_homotopy_category A := λ a,
    chain_complex.to_bounded_homotopy_category.obj (K.obj a),
  let P := _, change is_colimit P,
  let T : discrete.functor K.obj ⋙ chain_complex.to_bounded_homotopy_category ≅
    discrete.functor Q := discrete.nat_iso (λ _, iso.refl _),
  let P' := (cocones.precompose T.inv).obj P,
  suffices : is_colimit P',
  { exact is_colimit.precompose_inv_equiv _ _ this },
  apply is_colimit.of_iso_colimit (bounded_homotopy_category.is_colimit_cofan Q),
  swap, apply_instance,
  apply chain_complex_embed_cofan_iso,
end
