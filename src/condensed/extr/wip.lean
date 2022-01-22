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

def is_ExtrSheaf_of_types (P : ExtrDisc.{u}ᵒᵖ ⥤ Type u') : Prop :=
∀ (B : ExtrDisc.{u}) (ι : Type u) [fintype ι] (α : ι → ExtrDisc.{u})
  (f : Π i, α i ⟶ B) (hf : ∀ b : B, ∃ i (x : α i), f i x = b)
  (x : Π i, P.obj (op (α i)))
  (hx : ∀ (i j : ι) (Z : ExtrDisc) (g₁ : Z ⟶ α i) (g₂ : Z ⟶ α j),
    g₁ ≫ f _ = g₂ ≫ f _ → P.map g₁.op (x _) = P.map g₂.op (x _)),
∃! t : P.obj (op B), ∀ i, P.map (f i).op t = x _

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
