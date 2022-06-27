import for_mathlib.derived.les_facts
import liquid
import Lbar.functor
import condensed.projective_resolution
import condensed.condensify
import condensed.bd_lemma
import breen_deligne.eg

import for_mathlib.derived.ext_coproducts
import condensed.ab4
import Lbar.squares
import pseudo_normed_group.QprimeFP
import for_mathlib.acyclic
import free_pfpng.acyclic
import for_mathlib.SemiNormedGroup_ulift
import for_mathlib.bicartesian4

import for_mathlib.derived.Ext_lemmas

noncomputable theory

universes u

open opposite category_theory category_theory.limits
open_locale nnreal

variables (r r' : ℝ≥0)
variables [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]

abbreviation SemiNormedGroup.to_Cond (V : SemiNormedGroup.{u}) := Condensed.of_top_ab V

section

open bounded_homotopy_category

variables (BD : breen_deligne.data)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]

lemma ExtQprime_iso_aux_system_aux (c : ℝ≥0) (k i : ℤ) (hi : i > 0) :
  is_zero (((Ext' i).obj (op (((homological_complex.embed complex_shape.embedding.nat_down_int_up).obj
      ((QprimeFP_nat.{u} r' BD κ M).obj c)).X k))).obj V.to_Cond) :=
begin
  rcases k with (_|_)|_,
  { apply free_acyclic.{u} _ V i hi },
  { apply bounded_derived_category.Ext'_zero_left_is_zero, refine (is_zero_zero _).op },
  { apply free_acyclic.{u} _ V i hi },
end

open_locale zero_object

section

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables {ι : Type*} {c : complex_shape ι}
variables (C : homological_complex 𝓐 c)

def chain_complex_nat_has_homology_0
  (C : chain_complex 𝓐 ℕ) :
  has_homology (C.d 1 0) (0 : _ ⟶ 0) (C.homology 0) :=
sorry

def homological_complex_has_homology (i j k : ι) (hij : c.rel i j) (hjk : c.rel j k) :
  has_homology (C.d i j) (C.d j k) (C.homology j) :=
sorry

abbreviation chain_complex_nat_has_homology {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  (C : chain_complex 𝓐 ℕ) (n : ℕ) :
  has_homology (C.d (n+1+1) (n+1)) (C.d (n+1) n) (C.homology (n+1)) :=
homological_complex_has_homology C (n+1+1) (n+1) n rfl rfl

abbreviation cochain_complex_int_has_homology {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  (C : cochain_complex 𝓐 ℤ) (n : ℤ) :
  has_homology (C.d n (n+1)) (C.d (n+1) (n+1+1)) (C.homology (n+1)) :=
homological_complex_has_homology C n (n+1) (n+1+1) rfl rfl

end

def homology_embed_iso {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  (C : chain_complex 𝓐 ℕ) : Π (n : ℕ),
  ((homological_complex.embed complex_shape.embedding.nat_down_int_up).obj C).homology (-n) ≅
  C.homology n
| 0 :=
begin
  refine has_homology.iso _ (chain_complex_nat_has_homology_0 C),
  let C' := (homological_complex.embed complex_shape.embedding.nat_down_int_up).obj C,
  exact cochain_complex_int_has_homology C' (-(1:ℕ):ℤ),
end
| 1 :=
begin
  refine has_homology.iso _ (chain_complex_nat_has_homology C 0),
  let C' := (homological_complex.embed complex_shape.embedding.nat_down_int_up).obj C,
  exact cochain_complex_int_has_homology C' (-(1+1:ℕ):ℤ),
end
| (n+1+1) :=
begin
  refine has_homology.iso _ (chain_complex_nat_has_homology C (n+1)),
  let C' := (homological_complex.embed complex_shape.embedding.nat_down_int_up).obj C,
  exact cochain_complex_int_has_homology C' (-(n+1+1+1:ℕ):ℤ),
end

def map_homological_complex_embed
  {𝓐 𝓑 : Type*} [category 𝓐] [abelian 𝓐] [category 𝓑] [abelian 𝓑]
  (F : 𝓐 ⥤ 𝓑) [F.additive] :
  (homological_complex.embed complex_shape.embedding.nat_down_int_up) ⋙
  F.map_homological_complex _ ≅
  F.map_homological_complex _ ⋙
  (homological_complex.embed complex_shape.embedding.nat_down_int_up) :=
nat_iso.of_components (λ C, homological_complex.hom.iso_of_components
  (λ n, by { rcases n with ((_|n)|n),
    { exact iso.refl _ },
    { apply functor.map_zero_object },
    { exact iso.refl _ }, })
  begin
    rintro i j (rfl : _ = _), rcases i with (n|(_|n)),
    { apply is_zero.eq_of_tgt, apply is_zero_zero, },
    { erw [category.id_comp, category.comp_id], refl, },
    { erw [category.id_comp, category.comp_id], refl, },
  end)
begin
  intros C₁ C₂ f, ext ((_|n)|n) : 2,
  { rw [homological_complex.comp_f, homological_complex.comp_f],
    dsimp, erw [category.id_comp, category.comp_id], refl, },
  { apply is_zero.eq_of_tgt, apply is_zero_zero, },
  { rw [homological_complex.comp_f, homological_complex.comp_f],
    dsimp, erw [category.id_comp, category.comp_id], refl, },
end

-- this needs to be functorial in `c`
def ExtQprime_iso_aux_system_obj (c : ℝ≥0) (n : ℕ) :
  ((Ext n).obj (op $ (QprimeFP r' BD κ M).obj c)).obj ((single _ 0).obj V.to_Cond) ≅
  ((aux_system r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ).to_AbH n).obj (op c) :=
Ext_compute_with_acyclic _ _ (ExtQprime_iso_aux_system_aux r' BD κ M V c) _ ≪≫
begin
  refine (homology_functor _ _ (-n:ℤ)).map_iso _ ≪≫ _;
  sorry
end

attribute [reassoc] Ext_compute_with_acyclic_naturality

def ExtQprime_iso_aux_system (n : ℕ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ≅
  aux_system r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ ⋙
    (forget₂ _ Ab).map_homological_complex _ ⋙ homology_functor _ _ n :=
nat_iso.of_components (λ c, ExtQprime_iso_aux_system_obj r' BD κ M V (unop c) n)
begin
  intros c₁ c₂ h,
  dsimp only [ExtQprime_iso_aux_system_obj, iso.trans_hom],
  rw [functor.comp_map],
  -- rw [Ext_compute_with_acyclic_naturality_assoc],
  sorry
end

/-- The `Tinv` map induced by `M` -/
def ExtQprime.Tinv
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (n : ℤ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ⟶
  (QprimeFP r' BD κ₂ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) :=
whisker_right (nat_trans.op $ QprimeFP.Tinv BD _ _ M) _

/-- The `T_inv` map induced by `V` -/
def ExtQprime.T_inv [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (n : ℤ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ⟶
  (QprimeFP r' BD κ₂ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) :=
whisker_right (nat_trans.op $ QprimeFP.ι BD _ _ M) _ ≫ whisker_left _ ((Ext n).flip.map $ (single _ _).map $
  (Condensed.of_top_ab_map (normed_with_aut.T.inv).to_add_monoid_hom
  (normed_group_hom.continuous _)))

def ExtQprime.Tinv2 [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (n : ℤ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ⟶
  (QprimeFP r' BD κ₂ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) :=
ExtQprime.Tinv r' BD κ κ₂ M V n - ExtQprime.T_inv r r' BD κ κ₂ M V n

lemma ExtQprime_iso_aux_system_comm [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)] (n : ℕ) :
  (ExtQprime_iso_aux_system r' BD κ M V n).hom ≫
  whisker_right (aux_system.Tinv2.{u} r r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ₂ κ)
    ((forget₂ _ _).map_homological_complex _ ⋙ homology_functor Ab.{u+1} (complex_shape.up ℕ) n) =
  ExtQprime.Tinv2 r r' BD κ κ₂ M V n ≫
  (ExtQprime_iso_aux_system r' BD κ₂ M V n).hom :=
sorry

lemma ExtQprime_iso_aux_system_comm' [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)] (n : ℕ) :
  whisker_right (aux_system.Tinv2.{u} r r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ₂ κ)
    ((forget₂ _ _).map_homological_complex _ ⋙ homology_functor Ab.{u+1} (complex_shape.up ℕ) n) ≫
  (ExtQprime_iso_aux_system r' BD κ₂ M V n).inv =
  (ExtQprime_iso_aux_system r' BD κ M V n).inv ≫
  ExtQprime.Tinv2 r r' BD κ κ₂ M V n :=
begin
  rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp],
  apply ExtQprime_iso_aux_system_comm
end

end

section

def _root_.category_theory.functor.map_commsq
  {C D : Type*} [category C] [abelian C] [category D] [abelian D] (F : C ⥤ D) {X Y Z W : C}
  {f₁ : X ⟶ Y} {g₁ : X ⟶ Z} {g₂ : Y ⟶ W} {f₂ : Z ⟶ W} (sq : commsq f₁ g₁ g₂ f₂) :
  commsq (F.map f₁) (F.map g₁) (F.map g₂) (F.map f₂) :=
commsq.of_eq $ by rw [← F.map_comp, sq.w, F.map_comp]

end

section

variables {r'}
variables (BD : breen_deligne.package)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.data.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]

open bounded_homotopy_category

-- move me
instance eval'_is_bounded_above :
  ((homotopy_category.quotient (Condensed Ab) (complex_shape.up ℤ)).obj
    ((BD.eval' freeCond').obj M.to_Condensed)).is_bounded_above :=
by { delta breen_deligne.package.eval', refine ⟨⟨1, _⟩⟩, apply chain_complex.bounded_by_one }

variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

-- move me
instance sigma_Qprime_int_bounded_above :
  ((homotopy_category.quotient (Condensed Ab) (complex_shape.up ℤ)).obj
    (∐ λ (k : ulift ℕ), (QprimeFP_int r' BD.data κ M).obj (ι k))).is_bounded_above :=
begin
  refine ⟨⟨1, _⟩⟩,
  intros a ha,
  refine is_zero.of_iso _ (homotopy_category.coproduct_iso _ _),
  apply category_theory.is_zero_colimit,
  intro,
  exact chain_complex.bounded_by_one _ _ ha,
end

def Ext_Tinv2
  {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  {A B V : bounded_homotopy_category 𝓐}
  (Tinv : A ⟶ B) (ι : A ⟶ B) (T_inv : V ⟶ V) (i : ℤ) :
  ((Ext i).obj (op B)).obj V ⟶ ((Ext i).obj (op A)).obj V :=
(((Ext i).map Tinv.op).app V - (((Ext i).map ι.op).app V ≫ ((Ext i).obj _).map T_inv))

open category_theory.preadditive

def Ext_Tinv2_commsq
  {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  {A₁ B₁ A₂ B₂ V : bounded_homotopy_category 𝓐}
  (Tinv₁ : A₁ ⟶ B₁) (ι₁ : A₁ ⟶ B₁)
  (Tinv₂ : A₂ ⟶ B₂) (ι₂ : A₂ ⟶ B₂)
  (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (sqT : f ≫ Tinv₂ = Tinv₁ ≫ g) (sqι : f ≫ ι₂ = ι₁ ≫ g)
  (T_inv : V ⟶ V) (i : ℤ) :
  commsq
    (((Ext i).map g.op).app V)
    (Ext_Tinv2 Tinv₂ ι₂ T_inv i)
    (Ext_Tinv2 Tinv₁ ι₁ T_inv i)
    (((Ext i).map f.op).app V) :=
commsq.of_eq
begin
  delta Ext_Tinv2,
  simp only [comp_sub, sub_comp, ← nat_trans.comp_app, ← functor.map_comp, ← op_comp, sqT,
    ← nat_trans.naturality, ← nat_trans.naturality_assoc, category.assoc, sqι],
end

open category_theory.preadditive

lemma auux
  {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  {A₁ B₁ A₂ B₂ : cochain_complex 𝓐 ℤ}
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj A₁).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj B₁).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj A₂).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj B₂).is_bounded_above]
  {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂} {α : A₁ ⟶ A₂} {β : B₁ ⟶ B₂}
  (sq1 : commsq f₁ α β f₂) :
  of_hom f₁ ≫ of_hom β = of_hom α ≫ of_hom f₂ :=
begin
  have := sq1.w,
  apply_fun (λ f, (homotopy_category.quotient _ _).map f) at this,
  simp only [functor.map_comp] at this,
  exact this,
end

@[simp] lemma of_hom_id
  {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  {A : cochain_complex 𝓐 ℤ}
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj A).is_bounded_above] :
  of_hom (𝟙 A) = 𝟙 _ :=
by { delta of_hom, rw [category_theory.functor.map_id], refl }

lemma Ext_iso_of_bicartesian_of_bicartesian
  {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  {A₁ B₁ C A₂ B₂ : cochain_complex 𝓐 ℤ}
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj A₁).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj B₁).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj C).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj A₂).is_bounded_above]
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj B₂).is_bounded_above]
  {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C} (w₁ : ∀ n, short_exact (f₁.f n) (g₁.f n))
  {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C} (w₂ : ∀ n, short_exact (f₂.f n) (g₂.f n))
  (α : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (γ : C ⟶ C)
  (ιA : A₁ ⟶ A₂) (ιB : B₁ ⟶ B₂)
  (sq1 : commsq f₁ α β f₂) (sq2 : commsq g₁ β γ g₂)
  (sq1' : commsq f₁ ιA ιB f₂) (sq2' : commsq g₁ ιB (𝟙 _) g₂)
  (V : bounded_homotopy_category 𝓐) (T_inv : V ⟶ V)
  (i : ℤ)
  (H1 : (Ext_Tinv2_commsq (of_hom α) (of_hom ιA) (of_hom β) (of_hom ιB) (of_hom f₁) (of_hom f₂)
    (auux sq1) (auux sq1') T_inv i).bicartesian)
  (H2 : (Ext_Tinv2_commsq (of_hom α) (of_hom ιA) (of_hom β) (of_hom ιB) (of_hom f₁) (of_hom f₂)
    (auux sq1) (auux sq1') T_inv (i+1)).bicartesian) :
  is_iso (Ext_Tinv2 (of_hom γ) (𝟙 _) T_inv (i+1)) :=
begin
  have LES₁ := (((Ext_five_term_exact_seq' _ _ i V w₁).drop 2).pair.cons (Ext_five_term_exact_seq' _ _ (i+1) V w₁)),
  replace LES₁ := (((Ext_five_term_exact_seq' _ _ i V w₁).drop 1).pair.cons LES₁).extract 0 4,
  have LES₂ := (((Ext_five_term_exact_seq' _ _ i V w₂).drop 2).pair.cons (Ext_five_term_exact_seq' _ _ (i+1) V w₂)).extract 0 4,
  replace LES₂ := (((Ext_five_term_exact_seq' _ _ i V w₂).drop 1).pair.cons LES₂).extract 0 4,
  refine iso_of_bicartesian_of_bicartesian LES₂ LES₁ _ _ _ _ H1 H2,
  { apply commsq.of_eq, delta Ext_Tinv2, clear LES₁ LES₂,
    rw [sub_comp, comp_sub, ← functor.flip_obj_map, ← functor.flip_obj_map],
    rw ← Ext_δ_natural i V _ _ _ _ α β γ sq1.w sq2.w w₁ w₂,
    congr' 1,
    rw [← nat_trans.naturality, ← functor.flip_obj_map, category.assoc,
      Ext_δ_natural i V _ _ _ _ ιA ιB (𝟙 _) sq1'.w sq2'.w w₁ w₂],
    simp only [op_id, category_theory.functor.map_id, nat_trans.id_app,
      category.id_comp, of_hom_id, category.comp_id],
    erw [category.id_comp],
    symmetry,
    apply Ext_δ_natural', },
  { apply Ext_Tinv2_commsq,
    { exact auux sq2 },
    { exact auux sq2' }, },
end

def pi_Ext_iso_Ext_sigma (i : ℤ) :
  (∏ λ (k : ulift ℕ), ((QprimeFP r' BD.data κ₂ M).op ⋙
    (Ext i).flip.obj ((single (Condensed Ab) 0).obj V.to_Cond)).obj (op (ι k))) ≅
  ((Ext i).obj (op (of' (∐ λ (k : ulift ℕ), (QprimeFP_int r' BD.data κ₂ M).obj (ι k))))).obj
    ((single (Condensed Ab) 0).obj (Condensed.of_top_ab ↥V)) :=
(Ext_coproduct_iso
  (λ k : ulift ℕ, (QprimeFP r' BD.data κ₂ M).obj (ι k)) i
  ((single (Condensed Ab) 0).obj V.to_Cond)).symm ≪≫
  ((Ext i).flip.obj ((single (Condensed Ab) 0).obj V.to_Cond)).map_iso
(iso.op $
  (by exact iso.refl _ ) ≪≫
  (bounded_homotopy_category.is_colimit_cofan _).cocone_point_unique_up_to_iso
  (colimit.is_colimit _))

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
  refine commsq.bicartesian.of_iso
    (pi_Ext_iso_Ext_sigma _ _ _ _ _ _) (pi_Ext_iso_Ext_sigma _ _ _ _ _ _)
    (pi_Ext_iso_Ext_sigma _ _ _ _ _ _) (pi_Ext_iso_Ext_sigma _ _ _ _ _ _)
    _ _ _ _ H1;
  sorry
end

lemma Tinv2_iso_of_bicartesian [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
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
  have SES₁ := QprimeFP.short_exact BD κ₂ M ι hι,
  have SES₂ := QprimeFP.short_exact BD κ M ι hι,
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
  obtain ⟨ι, hι, H1, H2⟩ := H i,
  exact Tinv2_iso_of_bicartesian _ _ _ _ _ _ ι hι i H1 H2,
end

end

namespace Lbar

open ProFiltPseuNormGrpWithTinv₁ ProFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁
open bounded_homotopy_category

def condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
condensify (Fintype_Lbar.{u u} r' ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r')

def Tinv_sub (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V] (i : ℤ) :
  ((Ext' i).obj (op $ (Lbar.condensed.{u} r').obj S)).obj V.to_Cond ⟶
  ((Ext' i).obj (op $ (Lbar.condensed.{u} r').obj S)).obj V.to_Cond :=
((Ext' i).map ((condensify_Tinv _).app S).op).app _ -
((Ext' i).obj _).map (Condensed.of_top_ab_map (normed_with_aut.T.inv).to_add_monoid_hom
  (normed_group_hom.continuous _))

-- move me
@[simp] lemma _root_.category_theory.op_nsmul
  {C : Type*} [category C] [preadditive C] {X Y : C} (n : ℕ) (f : X ⟶ Y) :
  (n • f).op = n • f.op := rfl

-- move me
@[simp] lemma _root_.category_theory.op_sub
  {C : Type*} [category C] [preadditive C] {X Y : C} (f g : X ⟶ Y) :
  (f - g).op = f.op - g.op := rfl

-- move me
attribute [simps] Condensed.of_top_ab_map

variables (S : Profinite.{0}) (V : SemiNormedGroup.{0})
variables [complete_space V] [separated_space V]

def condensify_iso_extend :
  condensify (Fintype_Lbar.{0 0} r' ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r') ≅
  (Profinite.extend (Fintype_Lbar.{0 0} r')) ⋙
    (PFPNGT₁_to_CHFPNG₁ₑₗ r' ⋙ CHFPNG₁_to_CHFPNGₑₗ.{0} ⋙
  CompHausFiltPseuNormGrp.to_Condensed.{0}) :=
(((whiskering_left _ _ _).map_iso $
  Profinite.extend_commutes (Fintype_Lbar.{0 0} r') (PFPNGT₁_to_CHFPNG₁ₑₗ r')).app
    (CHFPNG₁_to_CHFPNGₑₗ.{0} ⋙ CompHausFiltPseuNormGrp.to_Condensed.{0})).symm

def condensify_iso_extend' :
  (condensify (Fintype_Lbar.{0 0} r' ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r')).obj S ≅
  ((Profinite.extend (Fintype_Lbar.{0 0} r')).obj S).to_Condensed :=
(condensify_iso_extend r').app S

section move_me

universes v u'

open Profinite

variables {C : Type u} [category.{v} C] (F : Fintype.{v} ⥤ C)
variables {D : Type u'} [category.{v} D]
variable [∀ X : Profinite, has_limit (X.fintype_diagram ⋙ F)]

@[reassoc]
lemma extend_commutes_comp_extend_extends' (G : C ⥤ D)
  [∀ X : Profinite.{v}, preserves_limits_of_shape (discrete_quotient X) G]
  [∀ X : Profinite.{v}, has_limit (X.fintype_diagram ⋙ F ⋙ G)] :
  whisker_left Fintype.to_Profinite (extend_commutes F G).hom =
  (functor.associator _ _ _).inv ≫ (whisker_right (extend_extends _).hom G) ≫
    (extend_extends _).inv :=
by rw [← category.assoc, iso.eq_comp_inv, extend_commutes_comp_extend_extends]

@[reassoc]
lemma extend_commutes_comp_extend_extends'' (G : C ⥤ D)
  [∀ X : Profinite.{v}, preserves_limits_of_shape (discrete_quotient X) G]
  [∀ X : Profinite.{v}, has_limit (X.fintype_diagram ⋙ F ⋙ G)] :
  whisker_left Fintype.to_Profinite (extend_commutes F G).inv =
  (extend_extends _).hom ≫ (whisker_right (extend_extends _).inv G) ≫
    (functor.associator _ _ _).hom :=
begin
  rw [← iso.inv_comp_eq, ← iso_whisker_left_inv, iso.comp_inv_eq, iso_whisker_left_hom,
    extend_commutes_comp_extend_extends', category.assoc, iso.hom_inv_id_assoc,
    ← iso_whisker_right_hom, ← iso_whisker_right_inv, iso.inv_hom_id_assoc],
end

end move_me

lemma condensify_Tinv_iso :
  condensify_Tinv (Fintype_Lbar.{0 0} r') ≫ (condensify_iso_extend r').hom =
  (condensify_iso_extend r').hom ≫ (@whisker_right _ _ _ _ _ _ _ _ (Tinv_nat_trans _) _) :=
begin
  delta Tinv_cond condensify_Tinv condensify_nonstrict condensify_iso_extend' condensify_iso_extend,
  ext S : 2,
  rw [iso.symm_hom, iso.app_inv, functor.map_iso_inv, nat_trans.comp_app, nat_trans.comp_app,
    whiskering_left_map_app_app, ← iso.app_inv, ← functor.map_iso_inv, iso.comp_inv_eq,
    functor.map_iso_inv, functor.map_iso_hom, functor.comp_map, functor.comp_map,
    whisker_right_app, whisker_right_app, ← functor.map_comp, ← functor.map_comp],
  congr' 1,
  rw [iso.app_inv, iso.app_hom, ← whisker_right_app, ← whisker_right_app,
    ← nat_trans.comp_app, ← nat_trans.comp_app],
  congr' 1,
  refine nonstrict_extend_ext _ _ (r'⁻¹) (1 * (r'⁻¹ * 1)) _ _ _,
  { intro X, apply nonstrict_extend_bound_by },
  { intro X,
    apply comphaus_filtered_pseudo_normed_group_hom.bound_by.comp,
    apply comphaus_filtered_pseudo_normed_group_hom.bound_by.comp,
    { apply strict_comphaus_filtered_pseudo_normed_group_hom.to_chfpsng_hom.bound_by_one },
    { apply Tinv_bound_by },
    { apply strict_comphaus_filtered_pseudo_normed_group_hom.to_chfpsng_hom.bound_by_one }, },
  { rw [whisker_left_comp, whisker_left_comp, ← whisker_right_left, ← whisker_right_left,
      extend_commutes_comp_extend_extends', extend_commutes_comp_extend_extends''],
    rw nonstrict_extend_whisker_left,

    ext X : 2,
    simp only [whisker_left_app, whisker_right_app, nat_trans.comp_app,
      functor.associator_hom_app, functor.associator_inv_app,
      category.id_comp, category.comp_id, category.assoc, functor.map_comp],
    slice_rhs 2 3 {},
    congr' 2,

    simp only [← iso.app_hom, ← iso.app_inv, ← functor.map_iso_hom, ← functor.map_iso_inv,
      category.assoc, iso.eq_inv_comp],

    ext x : 1,
    exact (comphaus_filtered_pseudo_normed_group_with_Tinv_hom.map_Tinv
      ((Profinite.extend_extends (Fintype_Lbar.{0 0} r')).app X).hom x).symm }
end

lemma condensify_Tinv_iso' :
  (condensify_Tinv (Fintype_Lbar.{0 0} r')).app S ≫ (condensify_iso_extend' r' S).hom =
  (condensify_iso_extend' r' S).hom ≫ ((Profinite.extend (Fintype_Lbar.{0 0} r')).obj S).Tinv_cond :=
begin
  have := condensify_Tinv_iso r',
  apply_fun (λ η, η.app S) at this,
  exact this,
end

def useful_commsq (i : ℤ) (ι : ulift.{1} ℕ → ℝ≥0) (hι : monotone ι) [normed_with_aut r V] :=
  shift_sub_id.commsq
    (ExtQprime.Tinv2 r r' breen_deligne.eg.data
      (λ c n, c * breen_deligne.eg.κ r r' n)
      (λ c n, r' * (c * breen_deligne.eg.κ r r' n))
      ((Lbar.functor.{0 0} r').obj S) V i) ι hι

section
open breen_deligne thm95.universal_constants

variables (i : ℕ)

lemma useful_commsq_bicartesian (ι : ulift.{1} ℕ → ℝ≥0) (hι : monotone ι) [normed_with_aut r V]
  (H1 : ∀ j, c₀ r r' eg (λ n, eg.κ r r' n) (eg.κ' r r') (i+1) ⟨ℤ⟩ ≤ ι j)
  (H2 : ∀ j, k (eg.κ' r r') i ^ 2 * ι j ≤ ι (j + 1))
  (H3 : ∀ j, k (eg.κ' r r') (i+1) ^ 2 * ι j ≤ ι (j + 1)) :
  (useful_commsq r r' S V i ι hι).bicartesian :=
begin
  apply shift_sub_id.bicartesian_iso _ _
    (ExtQprime_iso_aux_system r' _ _ _ V i).symm (ExtQprime_iso_aux_system r' _ _ _ V i).symm ι hι
    (ExtQprime_iso_aux_system_comm' _ _ _ _ _ _ _ _),
  rw [← whisker_right_twice],
  refine shift_sub_id.bicartesian (aux_system.incl'.{0 1} r r' _ _ _ (eg.κ r r')) _
    i ι hι _ _ _,
  { apply_with system_of_complexes.shift_eq_zero {instances := ff},
    swap 3, { apply thm94.explicit r r' _ _ (eg.κ' r r'), },
    any_goals { apply_instance },
    { intro j,
      refine le_trans _ ((c₀_mono _ _ _ _ _ _ (i+1)).out.trans (H1 j)),
      rw nat.add_sub_cancel, },
    { exact H2 } },
  { apply_with system_of_complexes.shift_eq_zero {instances := ff},
    swap 3, { apply thm94.explicit r r' _ _ (eg.κ' r r'), },
    any_goals { apply_instance },
    { exact H1 },
    { exact H3 } },
  { intros c n,
    let κ := eg.κ r r',
    apply aux_system.short_exact r r' _ _ _ (λ c n, r' * (c * κ n)) κ,
    intro c, dsimp, apply_instance, }
end

lemma bicartesian_of_is_zero {𝓒 : Type*} [category 𝓒] [abelian 𝓒]
  {A B C D : 𝓒} (f₁ : A ⟶ B) (g₁ : A ⟶ C) (g₂ : B ⟶ D) (f₂ : C ⟶ D) (h : commsq f₁ g₁ g₂ f₂)
  (hA : is_zero A) (hB : is_zero B) (hC : is_zero C) (hD : is_zero D) :
  h.bicartesian :=
begin
  delta commsq.bicartesian,
  apply_with short_exact.mk {instances:=ff},
  { refine ⟨λ X f g h, _⟩, apply hA.eq_of_tgt },
  { refine ⟨λ X f g h, _⟩, apply hD.eq_of_src },
  { apply exact_of_is_zero ((is_zero_biprod _ _ hB hC).of_iso (h.sum.iso (sum_str.biprod _ _))), }
end

lemma is_zero_pi {𝓒 : Type*} [category 𝓒] [abelian 𝓒] {ι : Type*} (f : ι → 𝓒) [has_product f]
  (hf : ∀ i, is_zero (f i)) :
  is_zero (∏ f) :=
begin
  rw is_zero_iff_id_eq_zero,
  ext,
  apply (hf j).eq_of_tgt,
end

lemma useful_commsq_bicartesian_neg  (ι : ulift.{1} ℕ → ℝ≥0) (hι : monotone ι) [normed_with_aut r V]
  (i : ℤ) (hi : i < 0) :
  (useful_commsq r r' S V i ι hι).bicartesian :=
begin
  have : 1 + i ≤ 0, { linarith only [hi] },
  apply bicartesian_of_is_zero;
  apply is_zero_pi; intro x;
  apply Ext_single_right_is_zero _ _ 1 _ _ (chain_complex.bounded_by_one _) this
end

lemma is_iso_sq {𝓒 : Type*} [category 𝓒] {X Y : 𝓒} (f₁ : X ⟶ X) (f₂ : Y ⟶ Y)
  (e : X ≅ Y) (h : f₁ ≫ e.hom = e.hom ≫ f₂) (h₁ : is_iso f₁) :
  is_iso f₂ :=
by { rw [← iso.inv_comp_eq] at h, rw ← h, apply_instance }

open category_theory.preadditive

lemma is_iso_sq' {𝓒 : Type*} [category 𝓒] [abelian 𝓒] [enough_projectives 𝓒]
  {X Y Z : bounded_homotopy_category 𝓒} (f₁ : X ⟶ X) (f₂ : Y ⟶ Y) (f₃ : Z ⟶ Z)
  (e : Y ≅ X) (h : e.hom ≫ f₁ = f₂ ≫ e.hom) (i : ℤ)
  (h₁ : is_iso (((Ext i).map f₁.op).app Z - ((Ext i).obj _).map f₃)) :
  is_iso (((Ext i).map f₂.op).app Z - ((Ext i).obj _).map f₃) :=
begin
  refine is_iso_sq _ _ ((functor.map_iso _ e.op).app _) _ h₁,
  rw [iso.app_hom, functor.map_iso_hom, sub_comp, comp_sub, nat_trans.naturality,
      ← nat_trans.comp_app, ← nat_trans.comp_app, ← functor.map_comp, ← functor.map_comp,
      iso.op_hom, ← op_comp, ← op_comp, h],
end

noncomputable
def ι' : ℕ → ℝ≥0
| 0 := max
        (c₀ r r' eg (λ (n : ℕ), eg.κ r r' n) (eg.κ' r r') (i + 1) ⟨ℤ⟩)
        (c₀ r r' eg (λ (n : ℕ), eg.κ r r' n) (eg.κ' r r') (i + 1 + 1) ⟨ℤ⟩)
| (j+1) := max
        (ι' j)
        (max
          (max
            (k (eg.κ' r r') i ^ 2 * ι' j)
            (k (eg.κ' r r') (i+1) ^ 2 * ι' j))
            ((k (eg.κ' r r') (i+1+1) ^ 2 * ι' j)))

lemma hι' : monotone (ι' r r' i) :=
begin
  apply monotone_nat_of_le_succ,
  rintro (_|j); apply le_max_left
end

lemma Hι1 : ∀ j,
  c₀ r r' eg (λ (n : ℕ), eg.κ r r' n) (eg.κ' r r') (i + 1) ⟨ℤ⟩ ≤ ι' r r' i j
| 0 := le_max_left _ _
| (j+1) := (Hι1 j).trans $ by { apply hι', apply nat.le_succ }

lemma Hι1' : ∀ j,
  c₀ r r' eg (λ (n : ℕ), eg.κ r r' n) (eg.κ' r r') (i + 1 + 1) ⟨ℤ⟩ ≤ ι' r r' i j
| 0 := le_max_right _ _
| (j+1) := (Hι1' j).trans $ by { apply hι', apply nat.le_succ }

lemma Hι2a : ∀ j,
  k (eg.κ' r r') i ^ 2 * ι' r r' i j ≤ ι' r r' i (j + 1) :=
by rintro (_|j); simp only [ι', le_max_iff, le_rfl, true_or, or_true]

lemma Hι2b : ∀ j,
  k (eg.κ' r r') (i + 1) ^ 2 * ι' r r' i j ≤ ι' r r' i (j + 1) :=
by rintro (_|j); simp only [ι', le_max_iff, le_rfl, true_or, or_true]

lemma Hι2c : ∀ j,
  k (eg.κ' r r') (i + 1 + 1) ^ 2 * ι' r r' i j ≤ ι' r r' i (j + 1) :=
by rintro (_|j); simp only [ι', le_max_iff, le_rfl, true_or, or_true]

def ι : ulift.{1} ℕ → ℝ≥0 := ι' r r' i ∘ ulift.down

lemma hι : monotone (ι r r' i) :=
λ j₁ j₂ h, by { delta ι, apply hι', exact h }

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem is_iso_Tinv_sub [normed_with_aut r V] : ∀ i, is_iso (Tinv_sub r r' S V i) :=
begin
  refine (Condensed.bd_lemma _ _ _ _).mpr _,
  intro i,
  refine is_iso_sq' _ _ _ (functor.map_iso _ $ condensify_iso_extend' _ _) _ _ _,
  { refine category_theory.functor.map _ _, refine Tinv_cond _ },
  { rw [functor.map_iso_hom, ← functor.map_comp, ← functor.map_comp, condensify_Tinv_iso'], },
  revert i,
  refine Tinv2_iso_of_bicartesian' r breen_deligne.eg
      (λ c n, c * breen_deligne.eg.κ r r' n)
      (λ c n, r' * (c * breen_deligne.eg.κ r r' n))
    ((Lbar.functor.{0 0} r').obj S) V _,
  rintro (i|(_|i)),
  { refine ⟨ι r r' i, hι r r' i, _, _⟩;
    apply useful_commsq_bicartesian,
    { rintro ⟨j⟩, apply Hι1 },
    { rintro ⟨j⟩, apply Hι2a },
    { rintro ⟨j⟩, apply Hι2b },
    { rintro ⟨j⟩, apply Hι1' },
    { rintro ⟨j⟩, apply Hι2b },
    { rintro ⟨j⟩, apply Hι2c } },
  { refine ⟨ι r r' 0, hι r r' 0, _, _⟩,
    { apply useful_commsq_bicartesian_neg, dec_trivial },
    { apply useful_commsq_bicartesian,
    { rintro ⟨j⟩, apply Hι1 },
    { rintro ⟨j⟩, apply Hι2a },
    { rintro ⟨j⟩, apply Hι2b }, }, },
  { refine ⟨λ _, 0, monotone_const, _, _⟩,
    { apply useful_commsq_bicartesian_neg, dec_trivial },
    { apply useful_commsq_bicartesian_neg,
      rw [int.neg_succ_of_nat_eq'],
      simp only [int.coe_nat_succ, neg_add_rev, sub_add_cancel, add_neg_lt_iff_le_add', add_zero],
      dec_trivial }, },
end

end

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem is_iso_Tinv2 [normed_with_aut r V]
  (hV : ∀ (v : V), (normed_with_aut.T.inv v) = 2 • v) :
  ∀ i, is_iso (((Ext' i).map ((condensify_Tinv2 (Fintype_Lbar.{0 0} r')).app S).op).app
    (Condensed.of_top_ab ↥V)) :=
begin
  intro i,
  rw [condensify_Tinv2_eq, ← functor.flip_obj_map, nat_trans.app_sub, category_theory.op_sub,
    nat_trans.app_nsmul,  category_theory.op_nsmul, two_nsmul, nat_trans.id_app, op_id,
    functor.map_sub, functor.map_add, category_theory.functor.map_id],
  convert is_iso_Tinv_sub r r' S V i using 2,
  suffices : Condensed.of_top_ab_map (normed_group_hom.to_add_monoid_hom normed_with_aut.T.inv) _ =
    2 • 𝟙 _,
  { rw [this, two_nsmul, functor.map_add, category_theory.functor.map_id], refl, },
  ext T f t,
  dsimp only [Condensed.of_top_ab_map_val, whisker_right_app, Ab.ulift_map_apply_down,
    add_monoid_hom.mk'_apply, continuous_map.coe_mk, function.comp_app],
  erw [hV, two_nsmul, two_nsmul],
  refl,
end

end Lbar
