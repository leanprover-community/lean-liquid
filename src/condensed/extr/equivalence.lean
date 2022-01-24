import condensed.extr.basic
import condensed.proetale_site
import condensed.basic
import category_theory.sites.induced_topology

import for_mathlib.presieve

open category_theory

universes u v' u'

def ExtrDisc.cover_dense :
  cover_dense proetale_topology.{u} ExtrDisc_to_Profinite.{u} :=
  cover_dense.mk $ λ U,
begin
  change ∃ R, _,
  obtain ⟨⟨T,hT,π,hπ⟩⟩ := enough_projectives.presentation U,
  dsimp at hT hπ,
  let R : presieve U := presieve.of_arrows (λ i : punit, T) (λ i, π),
  use R,
  split,
  { refine ⟨punit, infer_instance, λ i, T, λ i, π, λ x, ⟨punit.star, _⟩, rfl⟩,
    rw Profinite.epi_iff_surjective at hπ,
    exact hπ x },
  intros Y f hf,
  change nonempty _,
  rcases hf with ⟨a,b⟩,
  let t : presieve.cover_by_image_structure ExtrDisc_to_Profinite π := _,
  swap,
  { resetI,
    refine ⟨⟨T⟩, 𝟙 _, π, by simp⟩ },
  use t,
end

def ExtrDisc.proetale_topology : grothendieck_topology ExtrDisc.{u} :=
  ExtrDisc.cover_dense.induced_topology.{u}

@[derive category]
def ExtrSheaf (C : Type u') [category.{v'} C] := Sheaf ExtrDisc.proetale_topology.{u} C

-- TODO: cover_densed.Sheaf_equiv still has unecessary universe restrictions that can be relaxed.
noncomputable
def Condensed_ExtrSheaf_equiv (C : Type u') [category.{u+1} C] [limits.has_limits C] :
  ExtrSheaf.{u} C ≌ Condensed.{u} C :=
ExtrDisc.cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting
  ExtrDisc.cover_dense.locally_cover_dense.induced_topology_cover_preserving
  ExtrDisc.cover_dense.locally_cover_dense.induced_topology_cover_lifting

-- Sanity check
@[simp] lemma Condensed_ExtrSheaf_equiv_inverse_val (C : Type u') [category.{u+1} C]
  [limits.has_limits C] (F : Condensed.{u} C) :
  ((Condensed_ExtrSheaf_equiv C).inverse.obj F).val = ExtrDisc_to_Profinite.op ⋙ F.val := rfl

open opposite

theorem is_ExtrSheaf_of_types_of_is_sheaf_ExtrDisc_proetale_topology
  (F : ExtrDiscᵒᵖ ⥤ Type u') (H : presieve.is_sheaf ExtrDisc.proetale_topology F) :
  is_ExtrSheaf_of_types F :=
begin
  introsI B ι _ X f hf x hx,
  let S : presieve B := presieve.of_arrows X f,
  specialize H (sieve.generate S) _,
  { dsimp [ExtrDisc.proetale_topology],
    let R : presieve B.val := presieve.of_arrows (λ i, (X i).val) (λ i, (f i).val),
    use R,
    split,
    { use [ι, infer_instance, (λ i, (X i).val), (λ i, (f i).val), hf, rfl] },
    { intros Y f hf,
      rcases hf with ⟨i⟩,
      use [X i, f i, 𝟙 _],
      refine ⟨_, by simp⟩,
      use [X i, 𝟙 _, (f i), presieve.of_arrows.mk i],
      simp } },
  rw ← presieve.is_sheaf_for_iff_generate at H,
  let t : S.family_of_elements F := presieve.mk_family_of_elements_of_arrows X f F x,
  have ht : t.compatible := presieve.mk_family_of_elements_of_arrows_compatible X f F x hx,
  specialize H t ht,
  -- now use H.
  obtain ⟨tt,htt,htt'⟩ := H,
  refine ⟨tt,_,_⟩,
  { dsimp,
    intros i,
    specialize htt (f i) (presieve.of_arrows.mk i),
    rw htt,
    apply presieve.mk_family_of_elements_of_arrows_eval _ _ _ _ hx },
  { intros y hy,
    apply htt',
    intros Z f hf,
    rcases hf with ⟨i⟩,
    rw hy,
    symmetry,
    apply presieve.mk_family_of_elements_of_arrows_eval _ _ _ _ hx }
end

theorem is_seprated_of_is_ExtrSheaf_of_types
  (F : ExtrDiscᵒᵖ ⥤ Type u') (H : is_ExtrSheaf_of_types F) :
  presieve.is_separated ExtrDisc.proetale_topology F :=
begin
  intros B S hS x t₁ t₂ h₁ h₂,
  change proetale_topology _ _ at hS,
  rw ExtrDisc.cover_dense.locally_cover_dense.pushforward_cover_iff_cover_pullback at hS,
  obtain ⟨⟨T,hT⟩,rfl⟩ := hS,
  obtain ⟨R,hR,hRT⟩ := hT,
  obtain ⟨ι, _, X, f, surj, rfl⟩ := hR,
  resetI,
  let XX : ι → ExtrDisc := λ i, (X i).pres,
  let ff : Π i, (XX i) ⟶ B := λ i, ⟨(X i).pres_π ≫ f i⟩,
  have surjff : ∀ b : B, ∃ (i : ι) (q : XX i), (ff i) q = b,
  { intros b,
    obtain ⟨i,y,rfl⟩ := surj b,
    obtain ⟨z,rfl⟩ := (X i).pres_π_surjective y,
    use [i,z,rfl] },
  have hff : ∀ i, T (ff i).val,
  { intros i,
    dsimp [ff],
    apply sieve.downward_closed,
    apply hRT,
    exact presieve.of_arrows.mk i },
  let xx : Π i, F.obj (op (XX i)) := λ i, x _ _,
  swap, { exact ff i },
  swap, { exact hff i },
  specialize H B ι XX ff surjff xx _,
  { intros i j Z g₁ g₂ h,
    have hxcompat : x.compatible,
    { apply  presieve.is_compatible_of_exists_amalgamation,
      exact ⟨t₁, h₁⟩ },
    dsimp [presieve.family_of_elements.compatible] at hxcompat,
    dsimp [xx],
    specialize hxcompat g₁ g₂,
    apply hxcompat,
    exact h },
  obtain ⟨t,ht,ht'⟩ := H,
  have ht₁ : t₁ = t,
  { apply ht',
    intros i,
    apply h₁ },
  have ht₂ : t₂ = t,
  { apply ht',
    intros i,
    apply h₂ },
  rw [ht₁, ht₂]
end

theorem is_sheaf_ExtrDisc_proetale_topology_of_is_ExtrSheaf_of_types
  (F : ExtrDiscᵒᵖ ⥤ Type u') (H : is_ExtrSheaf_of_types F) :
  presieve.is_sheaf ExtrDisc.proetale_topology F :=
begin
  have hF : presieve.is_separated ExtrDisc.proetale_topology F,
  { apply is_seprated_of_is_ExtrSheaf_of_types,
    assumption },
  intros B S hS,
  rw ← presieve.is_separated_for_and_exists_is_amalgamation_iff_sheaf_for,
  split, { apply hF _ hS },
  intros x hx,
  change proetale_topology _ _ at hS,
  rw ExtrDisc.cover_dense.locally_cover_dense.pushforward_cover_iff_cover_pullback at hS,
  obtain ⟨⟨T,hT⟩,rfl⟩ := hS,
  obtain ⟨R,hR,hRT⟩ := hT,
  obtain ⟨ι, _, X, f, surj, rfl⟩ := hR,
  resetI,
  let XX : ι → ExtrDisc := λ i, (X i).pres,
  let ff : Π i, (XX i) ⟶ B := λ i, ⟨(X i).pres_π ≫ f i⟩,
  have surjff : ∀ b : B, ∃ (i : ι) (q : XX i), (ff i) q = b,
  { intros b,
    obtain ⟨i,y,rfl⟩ := surj b,
    obtain ⟨z,rfl⟩ := (X i).pres_π_surjective y,
    use [i,z,rfl] },
  have hff : ∀ i, T (ff i).val,
  { intros i,
    dsimp [ff],
    apply sieve.downward_closed,
    apply hRT,
    exact presieve.of_arrows.mk i },
  let xx : Π i, F.obj (op (XX i)) := λ i, x _ _,
  swap, { exact ff i },
  swap, { exact hff i },
  specialize H B ι XX ff surjff xx _,
  { intros i j Z g₁ g₂ h,
    dsimp [presieve.family_of_elements.compatible] at hx,
    dsimp [xx],
    specialize hx g₁ g₂,
    apply hx,
    exact h },
  obtain ⟨t,ht,ht'⟩ := H,
  use t,
  intros Y f hf,
  let PP : ι → Profinite := λ i, Profinite.pullback f.val (ff i).val,
  let QQ : ι → ExtrDisc := λ i, (PP i).pres,
  let ππ : Π i, (QQ i) ⟶ XX i := λ i, ⟨(PP i).pres_π ≫ Profinite.pullback.snd _ _⟩,
  let gg : Π i, (QQ i) ⟶ Y := λ i,
    ⟨(PP i).pres_π ≫ Profinite.pullback.fst _ _⟩,
  let W : sieve Y := sieve.generate (presieve.of_arrows QQ gg),
  specialize hF W _,
  { change ∃ _, _,
    use presieve.of_arrows (λ i, (QQ i).val) (λ i, (gg i).val),
    split,
    { use [ι, infer_instance, (λ i, (QQ i).val), (λ i, (gg i).val)],
      refine ⟨_,rfl⟩,
      intros y,
      obtain ⟨i,t,ht⟩ := surj (f y),
      obtain ⟨w,hw⟩ := (X i).pres_π_surjective t,
      obtain ⟨z,hz⟩ := (PP i).pres_π_surjective ⟨⟨y,w⟩,_⟩,
      swap, { dsimp, rw hw, exact ht.symm },
      use [i, z],
      dsimp [gg],
      rw hz, refl },
    { intros Z f hf,
      obtain ⟨i⟩ := hf,
      change ∃ _, _,
      use [(QQ i), gg i, 𝟙 _],
      split,
      { apply sieve.le_generate,
        apply presieve.of_arrows.mk },
      { ext1, simp } } },
  dsimp [presieve.is_separated_for] at hF,
  have : ∀ (Z : ExtrDisc) (g : Z ⟶ Y) (hg : W g),
    ∃ (i : ι) (e : Z ⟶ QQ i), g = e ≫ gg i,
  { intros Z g hg,
    obtain ⟨QQ',e₁,e₂,h1,h2⟩ := hg,
    obtain ⟨i⟩ := h1,
    use [i, e₁, h2.symm] },
  choose ii ee hee using this,
  let y : presieve.family_of_elements F W := λ Z g hg,
    F.map (ee _ _ hg ≫ ππ _).op (xx (ii _ _ hg)),
  have hy : y.compatible,
  { intros T₁ T₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w,
    dsimp [y, xx],
    simp only [← F.map_comp, ← op_comp],
    change (F.map _ ≫ F.map _) _ = (F.map _ ≫ F.map _) _,
    simp only [← F.map_comp, ← op_comp],
    apply hx,
    apply_fun (λ e, e ≫ f) at w,
    simp only [category.assoc] at w ⊢,
    convert w using 2,
    { ext1,
      dsimp [ππ, ff],
      simp only [category.assoc],
      rw [← Profinite.pullback.condition, ← category.assoc],
      change ((ee T₁ f₁ h₁ ≫ gg _) ≫ f).val = (f₁ ≫ f).val,
      congr' 2,
      symmetry,
      apply hee },
    { ext1,
      dsimp [ππ, ff],
      simp only [category.assoc],
      rw [← Profinite.pullback.condition, ← category.assoc],
      change ((ee T₂ f₂ h₂ ≫ gg _) ≫ f).val = (f₂ ≫ f).val,
      congr' 2,
      symmetry,
      apply hee } },
  apply hF y (F.map f.op t) (x f hf),
  { intros L e he,
    dsimp [y],
    have := hee _ _ he,
    conv_lhs { rw this },
    rw ← ht,
    simp only [← comp_apply, ← F.map_comp, ← op_comp],
    change (F.map _ ≫ F.map _) _ = (F.map _ ≫ F.map _) _,
    simp_rw [← F.map_comp, ← op_comp],
    congr' 2,
    simp only [category.assoc],
    congr' 1,
    ext1,
    dsimp,
    simp [Profinite.pullback.condition] },
  { intros L e he,
    dsimp [y],
    have := hee _ _ he,
    conv_lhs { rw this },
    dsimp only [xx],
    simp only [← F.map_comp, ← op_comp],
    apply hx,
    simp only [category.assoc],
    congr' 1,
    ext1,
    dsimp,
    simp [Profinite.pullback.condition] }
end

theorem is_ExtrSheaf_of_types_iff (F : ExtrDiscᵒᵖ ⥤ Type u') :
  is_ExtrSheaf_of_types F ↔ presieve.is_sheaf ExtrDisc.proetale_topology F :=
⟨λ H, is_sheaf_ExtrDisc_proetale_topology_of_is_ExtrSheaf_of_types _ H,
  λ H, is_ExtrSheaf_of_types_of_is_sheaf_ExtrDisc_proetale_topology _ H⟩

theorem is_ExtrSheaf_iff (C : Type u') [category.{v'} C]
  (F : ExtrDiscᵒᵖ ⥤ C) :
  is_ExtrSheaf F ↔ presheaf.is_sheaf ExtrDisc.proetale_topology F :=
begin
  rw is_ExtrSheaf_iff_forall_yoneda,
  apply forall_congr (λ T, _),
  apply is_ExtrSheaf_of_types_iff,
end

theorem is_sheaf_ExtrDisc_proetale_iff_product_condition
  (C : Type u') [category.{v'} C] [limits.has_finite_products C]
  (F : ExtrDiscᵒᵖ ⥤ C) :
  presheaf.is_sheaf ExtrDisc.proetale_topology F ↔ ExtrDisc.finite_product_condition F :=
begin
  rw ← is_ExtrSheaf_iff,
  rw is_ExtrSheaf_iff_product_condition,
end

structure ExtrSheafProd (C : Type.{u'}) [category.{v'} C] [limits.has_finite_products C] :=
(val : ExtrDisc.{u}ᵒᵖ ⥤ C)
(cond : ExtrDisc.finite_product_condition val)

namespace ExtrSheafProd

variables (C : Type.{u'}) [category.{v'} C] [limits.has_finite_products C]

@[ext]
structure hom (X Y : ExtrSheafProd C) :=
mk :: (val : X.val ⟶ Y.val)

@[simps]
instance : category (ExtrSheafProd C) :=
{ hom := hom C,
  id := λ X, ⟨𝟙 _⟩,
  comp := λ X Y Z f g, ⟨f.val ≫ g.val⟩ }

end ExtrSheafProd

-- TODO: Break up this structure into individual components... it's too slow as is.
def ExtrSheaf_ExtrSheafProd_equiv (C : Type.{u'}) [category.{v'} C] [limits.has_finite_products C] :
  ExtrSheaf C ≌ ExtrSheafProd C :=
{ functor :=
  { obj := λ F, ⟨F.val,
      (is_sheaf_ExtrDisc_proetale_iff_product_condition _ _).mp F.2⟩,
    map := λ F G f, ⟨f.val⟩,
    map_id' := λ X, by { ext1, refl },
    map_comp' := λ X Y Z f g, by { ext1, refl } },
  inverse :=
  { obj := λ F, ⟨F.val,
      (is_sheaf_ExtrDisc_proetale_iff_product_condition _ _).mpr F.2⟩,
    map := λ F G f, ⟨f.val⟩,
    map_id' := λ X, by { ext1, refl },
    map_comp' := λ X Y Z f g, by { ext1, refl } },
  unit_iso := nat_iso.of_components
    (λ X,
    { hom := ⟨𝟙 _⟩,
      inv := ⟨𝟙 _⟩,
      hom_inv_id' := by { ext1, dsimp, simp },
      inv_hom_id' := by { ext1, dsimp, simp } })
    begin
      intros X Y f,
      ext1,
      dsimp,
      simp,
    end,
  counit_iso := nat_iso.of_components
    (λ X,
    { hom := ⟨𝟙 _⟩,
      inv := ⟨𝟙 _⟩,
      hom_inv_id' := by { ext1, dsimp, simp },
      inv_hom_id' := by { ext1, dsimp, simp } })
    begin
      intros X Y f,
      ext1,
      dsimp,
      simp,
    end,
  functor_unit_iso_comp' := begin
    intros,
    ext1,
    dsimp,
    simp,
  end } .

noncomputable
def Condensed_ExtrSheafProd_equiv (C : Type.{u'}) [category.{u+1} C] [limits.has_limits C] :
  Condensed.{u} C ≌ ExtrSheafProd.{u} C :=
(Condensed_ExtrSheaf_equiv C).symm.trans (ExtrSheaf_ExtrSheafProd_equiv C)

-- Sanity check
@[simp]
lemma Condensed_ExtrSheafProd_equiv_functor_obj_val
  {C : Type.{u'}} [category.{u+1} C] [limits.has_limits C] (F : Condensed C) :
  ((Condensed_ExtrSheafProd_equiv C).functor.obj F).val = ExtrDisc_to_Profinite.op ⋙ F.val := rfl

def ExtrSheafProd_to_presheaf (C : Type.{u'}) [category.{v'} C]
  [limits.has_finite_products C] :
  ExtrSheafProd.{u} C ⥤ ExtrDisc.{u}ᵒᵖ ⥤ C :=
{ obj := λ F, F.val,
  map := λ F G f, f.val,
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g, rfl }

instance (C : Type.{u'}) [category.{v'} C]
  [limits.has_finite_products C] : full (ExtrSheafProd_to_presheaf C) := sorry

instance (C : Type.{u'}) [category.{v'} C]
  [limits.has_finite_products C] : faithful (ExtrSheafProd_to_presheaf C) := sorry

open category_theory.limits
--set_option pp.universes true

section
variables {C : Type u'} [category.{u+1} C] [has_limits C]
  [has_zero_morphisms C] [has_finite_biproducts C]

open_locale classical

lemma finite_product_condition_holds_for_colimit
  {J : Type (u+1)} [small_category J] (K : J ⥤ ExtrSheafProd.{u} C)
  [has_colimit (K ⋙ ExtrSheafProd_to_presheaf C)] :
  ExtrDisc.finite_product_condition (colimit (K ⋙ ExtrSheafProd_to_presheaf C)) :=
begin
  sorry
end

noncomputable
instance ExtrSheafProd_to_presheaf_creates_colimit
  {J : Type (u+1)} [small_category J] (K : J ⥤ ExtrSheafProd.{u} C)
  [has_colimit (K ⋙ ExtrSheafProd_to_presheaf _)]:
  creates_colimit K (ExtrSheafProd_to_presheaf.{u} C) :=
creates_colimit_of_fully_faithful_of_iso
⟨colimit (K ⋙ ExtrSheafProd_to_presheaf _), finite_product_condition_holds_for_colimit _⟩ $
eq_to_iso rfl

noncomputable
instance ExtrSheafProd_to_presheaf_creates_colimits_of_shape
  {J : Type (u+1)} [small_category J] :
  creates_colimits_of_shape J (ExtrSheafProd_to_presheaf.{u} C) :=
⟨λ K,
{ reflects := begin
    intros c hc,
    haveI : has_colimit (K ⋙ ExtrSheafProd_to_presheaf C) := has_colimit.mk ⟨_,hc⟩,
    apply is_colimit_of_reflects (ExtrSheafProd_to_presheaf.{u} C),
    assumption,
  end,
  lifts := λ c hc,
  { lifted_cocone := begin
      haveI : has_colimit (K ⋙ ExtrSheafProd_to_presheaf C) := has_colimit.mk ⟨_,hc⟩,
      exact lift_colimit hc,
    end,
    valid_lift := begin
      haveI : has_colimit (K ⋙ ExtrSheafProd_to_presheaf C) := has_colimit.mk ⟨_,hc⟩,
      apply lifted_colimit_maps_to_original,
    end } }⟩

noncomputable
instance ExtrSheafProd_to_presheaf_creates_colimits :
  creates_colimits (ExtrSheafProd_to_presheaf.{u} C) := by constructor

-- Forgetting to presheaves, and restricting to `ExtrDisc` creates colimits.
noncomputable
instance Condensed_to_ExtrDisc_presheaf_creates_colimits :
  creates_colimits
  ((Sheaf_to_presheaf _ _ : Condensed C ⥤ _) ⋙
  (whiskering_left _ _ _).obj (ExtrDisc_to_Profinite.op)) :=
begin
  change creates_colimits
    ((Condensed_ExtrSheafProd_equiv C).functor ⋙ ExtrSheafProd_to_presheaf C),
  apply_with category_theory.comp_creates_colimits { instances := ff}; apply_instance
end

end
