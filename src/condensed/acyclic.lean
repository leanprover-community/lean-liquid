import for_mathlib.derived.Ext_lemmas
import for_mathlib.Cech.homotopy
import for_mathlib.acyclic
import for_mathlib.exact_seq4
import for_mathlib.cech
import for_mathlib.chain_complex_exact
import for_mathlib.abelian_sheaves.exact
import for_mathlib.Cech.homotopy
import for_mathlib.wide_pullback_iso
import for_mathlib.equivalence_additive
import for_mathlib.op

import condensed.adjunctions2
import condensed.projective_resolution
import condensed.extr.equivalence
.

noncomputable theory

universes u

open category_theory category_theory.limits homotopy_category opposite
open function (surjective)

namespace condensed

set_option pp.universes true

-- ANNOYING!
instance presheaf_abelian : abelian (Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) :=
category_theory.functor_category_is_abelian.{(u+2) u (u+1)}

-- ANNOYING!
instance ExtrDisc_presheaf_abelian : abelian (ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1}) :=
category_theory.functor_category_is_abelian.{(u+2) u (u+1)}

instance ExtrSheaf_abelian' : abelian (Sheaf ExtrDisc.proetale_topology.{u} Ab.{u+1}) :=
category_theory.Sheaf.abelian.{(u+2) u (u+1)}

instance ExtrSheaf_abelian : abelian (ExtrSheaf.{u} Ab.{u+1}) :=
category_theory.Sheaf.abelian.{(u+2) u (u+1)}

def Profinite_to_presheaf_Ab : Profinite.{u} ⥤ Profinite.{u}ᵒᵖ ⥤ Ab.{u+1} :=
yoneda ⋙ (whiskering_right _ _ _).obj (ulift_functor.{u+1} ⋙ AddCommGroup.free)

def Profinite_to_ExtrDisc_presheaf : Profinite.{u} ⥤ ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1) :=
yoneda ⋙ (whiskering_left _ _ _).obj ExtrDisc_to_Profinite.op ⋙
  (whiskering_right _ _ _).obj ulift_functor.{u+1}

def Profinite_to_ExtrDisc_presheaf_Ab : Profinite.{u} ⥤ ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1} :=
yoneda ⋙ (whiskering_left _ _ _).obj ExtrDisc_to_Profinite.op ⋙
  (whiskering_right _ _ _).obj (ulift_functor.{u+1} ⋙ AddCommGroup.free)

def unsheafified_free_Cech' (F : arrow Profinite.{u}) :
  chain_complex (Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) ℕ :=
simplicial_object.augmented.to_complex $
(((simplicial_object.augmented.whiskering _ _).obj Profinite_to_presheaf_Ab).obj
  F.augmented_cech_nerve)

def unsheafified_free_ExtrDiscr_Cech (F : arrow Profinite.{u}) :
  chain_complex (ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1}) ℕ :=
simplicial_object.augmented.to_complex $
(((simplicial_object.augmented.whiskering _ _).obj Profinite_to_ExtrDisc_presheaf_Ab).obj
  F.augmented_cech_nerve)

def free_Cech' (F : arrow Profinite.{u}) :
  chain_complex (Condensed.{u} Ab.{u+1}) ℕ :=
(((simplicial_object.augmented.whiskering _ _).obj
  (Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab)).obj
  F.augmented_cech_nerve).to_complex

def free_ExtrDisc_Cech' (F : arrow Profinite.{u}) :
  chain_complex (ExtrSheaf.{u} Ab.{u+1}) ℕ :=
(((simplicial_object.augmented.whiskering _ _).obj
  (Profinite_to_ExtrDisc_presheaf_Ab ⋙ presheaf_to_Sheaf _ _)).obj
  F.augmented_cech_nerve).to_complex

def free_Cech (F : arrow Profinite.{u}) :
  chain_complex (Condensed.{u} Ab.{u+1}) ℤ :=
(homological_complex.embed $ complex_shape.embedding.nat_down_int_down).obj (free_Cech' F)

instance Condensed_ExtrSheaf_equiv_additive :
  functor.additive (Condensed_ExtrSheaf_equiv Ab.{u+1}).inverse :=
by constructor

-- SELFCONTAINED
def whiskering_Cech_comp_iso
  {C : Type*} [category C] {𝓐 : Type*} [category 𝓐] [abelian 𝓐] {𝓑 : Type*} [category 𝓑] [abelian 𝓑]
  (f : arrow C) [∀ (n : ℕ),
    has_wide_pullback f.right (λ (i : ulift (fin (n + 1))), f.left) (λ (i : ulift (fin (n + 1))), f.hom)]
  (F : C ⥤ 𝓐) (G : 𝓐 ⥤ 𝓑) (H : C ⥤ 𝓑) (E : F ⋙ G ≅ H) [G.additive] :
  (G.map_homological_complex _).obj ((((simplicial_object.augmented.whiskering _ _).obj F).obj
    f.augmented_cech_nerve).to_complex) ≅
  (((simplicial_object.augmented.whiskering _ _).obj H).obj f.augmented_cech_nerve).to_complex :=
homological_complex.hom.iso_of_components
(λ i,
match i with
| 0 := E.app _
| i+1 := E.app _
end)
begin
  rintros i j (rfl : j + 1 = i),
  dsimp only [functor.map_homological_complex_obj_d,
    unsheafified_free_ExtrDiscr_Cech, free_ExtrDisc_Cech',
    simplicial_object.augmented.to_complex],
  rw [chain_complex.of_d, chain_complex.of_d],
  cases j,
  { dsimp only [whiskering_Cech_comp_iso._match_1],
    dsimp only [simplicial_object.augmented.to_complex_d,
      simplicial_object.augmented.whiskering_obj_2,
      simplicial_object.augmented.whiskering_obj,
      nat_trans.comp_app, whisker_right_app, functor.const_comp_hom_app],
    rw [category.comp_id, category.comp_id, nat_iso.app_hom, ← E.hom.naturality],
    refl },
  {
    dsimp only [whiskering_Cech_comp_iso._match_1],
    dsimp only [simplicial_object.augmented.to_complex_d,
      simplicial_object.augmented.drop_obj,
      simplicial_object.augmented.whiskering_obj_2,
      simplicial_object.augmented.whiskering_obj,
      simplicial_object.whiskering_obj_obj_map,
      simplicial_object.boundary,
      nat_iso.app_hom],
    simp only [functor.map_sum, functor.map_zsmul, preadditive.comp_sum,
      preadditive.comp_zsmul, preadditive.sum_comp, preadditive.zsmul_comp],
    apply finset.sum_congr rfl, intros _ _,
    erw ← E.hom.naturality,
    refl, },
end


def free_Cech'_iso_ExtrDisc (F : arrow Profinite.{u}) :
  ((Condensed_ExtrSheaf_equiv _).inverse.map_homological_complex _).obj (free_Cech' F) ≅
  free_ExtrDisc_Cech' F :=
let e := ExtrDisc_sheafification_iso in
whiskering_Cech_comp_iso F
  (Profinite_to_Condensed.{u} ⋙ CondensedSet_to_Condensed_Ab.{u})
  ((Condensed_ExtrSheaf_equiv.{u u+2} Ab.{u+1}).inverse)
  (Profinite_to_ExtrDisc_presheaf_Ab.{u} ⋙ presheaf_to_Sheaf.{u+2 u u+1} ExtrDisc.proetale_topology.{u} Ab.{u+1}) $
nat_iso.of_components
(λ S, e.symm.app _)
begin
  intros S T f,
  dsimp only [nat_iso.app_hom],
  erw e.symm.hom.naturality,
  refl,
end

instance presheaf_to_Sheaf_additive :
  (presheaf_to_Sheaf.{u+2 u u+1} ExtrDisc.proetale_topology.{u} Ab.{u+1}).additive :=
category_theory.Sheaf.presheaf_to_Sheaf_additive

-- SELFCONTAINED
def acyclic_of_exact.induction_step_ex₂_aux
  {C : Type*} [category C] {𝓐 : Type*} [category 𝓐] [abelian 𝓐] {𝓑 : Type*} [category 𝓑] [abelian 𝓑]
  (f : arrow C) [∀ (n : ℕ),
    has_wide_pullback f.right (λ (i : ulift (fin (n + 1))), f.left) (λ (i : ulift (fin (n + 1))), f.hom)]
  (F : C ⥤ 𝓐) (G : 𝓐ᵒᵖ ⥤ 𝓑) [G.additive] :
  (G.map_homological_complex _).obj ((((simplicial_object.augmented.whiskering _ _).obj F).obj
    f.augmented_cech_nerve).to_complex).op ≅
  (((cosimplicial_object.augmented.whiskering _ _).obj (F.op ⋙ G)).obj
    f.augmented_cech_nerve.right_op).to_cocomplex :=
homological_complex.hom.iso_of_components
(λ i,
match i with
| 0 := iso.refl _
| i+1 := iso.refl _
end)
begin
  rintros i j (rfl : i + 1 = j),
  dsimp only [functor.map_homological_complex_obj_d,
    unsheafified_free_ExtrDiscr_Cech, free_ExtrDisc_Cech',
    cosimplicial_object.augmented.to_cocomplex,
    simplicial_object.augmented.to_complex, homological_complex.op_d],
  rw [cochain_complex.of_d, chain_complex.of_d],
  cases i,
  { refine (category.id_comp _).trans ((category.comp_id _).trans _).symm,
    dsimp only [simplicial_object.augmented.to_complex_d,
      cosimplicial_object.augmented.to_cocomplex_d,
      simplicial_object.augmented.whiskering_obj_2,
      simplicial_object.augmented.whiskering_obj,
      cosimplicial_object.augmented.whiskering_obj_2,
      cosimplicial_object.augmented.whiskering_obj,
      nat_trans.comp_app, whisker_right_app,
      functor.const_comp_hom_app, functor.const_comp_inv_app],
    rw [category.comp_id, category.id_comp],
    refl, },
  { refine (category.id_comp _).trans ((category.comp_id _).trans _).symm,
    dsimp only [simplicial_object.augmented.to_complex_d,
      simplicial_object.augmented.drop_obj,
      simplicial_object.augmented.whiskering_obj_2,
      simplicial_object.augmented.whiskering_obj,
      simplicial_object.whiskering_obj_obj_map,
      simplicial_object.boundary,
      cosimplicial_object.augmented.to_cocomplex_d,
      cosimplicial_object.augmented.drop_obj,
      cosimplicial_object.augmented.whiskering_obj_2,
      cosimplicial_object.augmented.whiskering_obj,
      cosimplicial_object.whiskering_obj_obj_map,
      cosimplicial_object.coboundary],
    simp only [G.map_sum, G.map_zsmul, op_sum, op_zsmul],
    refl, },
end

def free_ExtrDisc_Cech'_iso (F : arrow Profinite.{u}) :
  free_ExtrDisc_Cech' F ≅
  ((presheaf_to_Sheaf _ _).map_homological_complex _).obj (unsheafified_free_ExtrDiscr_Cech F) :=
(whiskering_Cech_comp_iso F _ _ _ $ iso.refl _).symm
/-
homological_complex.hom.iso_of_components
(λ i,
match i with
| 0 := iso.refl _
| i+1 := iso.refl _
end)
begin
  rintros i j (rfl : j + 1 = i),
  dsimp only [functor.map_homological_complex_obj_d,
    unsheafified_free_ExtrDiscr_Cech, free_ExtrDisc_Cech',
    simplicial_object.augmented.to_complex],
  rw [chain_complex.of_d, chain_complex.of_d],
  cases j,
  { refine (category.id_comp _).trans ((category.comp_id _).trans _).symm,
    dsimp only [simplicial_object.augmented.to_complex_d,
      simplicial_object.augmented.whiskering_obj_2,
      simplicial_object.augmented.whiskering_obj,
      nat_trans.comp_app, whisker_right_app, functor.const_comp_hom_app],
    rw [category.comp_id, category.comp_id],
    refl, },
  { refine (category.id_comp _).trans ((category.comp_id _).trans _).symm,
    dsimp only [simplicial_object.augmented.to_complex_d,
      simplicial_object.augmented.drop_obj,
      simplicial_object.augmented.whiskering_obj_2,
      simplicial_object.augmented.whiskering_obj,
      simplicial_object.whiskering_obj_obj_map,
      simplicial_object.boundary],
    simp only [functor.map_sum, functor.map_zsmul],
    refl, },
end
-/

/-
def free_Cech_iso (F : arrow Profinite.{u}) :
  free_Cech F ≅ (homological_complex.embed $ complex_shape.embedding.nat_down_int_down).obj
  ((presheaf_to_Condensed_Ab.map_homological_complex _).obj
  (unsheafified_free_Cech' F)) :=
homological_complex.hom.iso_of_components
(λ i,
match i with
| int.of_nat 0 := iso.refl _
| int.of_nat (n+1) := iso.refl _
| -[1+i] := iso.refl _
end)
(by admit)
-/

-- SO ANNOYING
instance evaluation_additive (X : ExtrDisc.{u}) :
  functor.additive ((evaluation ExtrDisc.{u}ᵒᵖ Ab.{u+1}).obj (op X)) :=
category_theory.evaluation_additive.{(u+2) u (u+1)} _

def evaluated_free_ExtrDisc_Cech (F : arrow Profinite.{u}) (X : ExtrDisc.{u}) :
  chain_complex Ab.{u+1} ℕ :=
(((simplicial_object.augmented.whiskering _ _).obj
  AddCommGroup.free).obj $
  ((Profinite_to_ExtrDisc_presheaf.flip.obj (op X)).map_arrow.obj F).augmented_cech_nerve).to_complex

.

def yet_another_iso (F : arrow Profinite.{u}) (X : ExtrDisc.{u}) :
  (((evaluation.{u u+1 u+1 u+2} ExtrDisc.{u}ᵒᵖ Ab.{u+1}).obj
  (op X)).map_homological_complex
  (complex_shape.down.{0} ℕ)).obj
  (unsheafified_free_ExtrDiscr_Cech.{u} F) ≅
  evaluated_free_ExtrDisc_Cech F X :=
homological_complex.hom.iso_of_components
(λ i,
match i with
| 0 := iso.refl _
| i+1 := begin apply AddCommGroup.free.map_iso, apply ulift_wide_pullback_iso, end
end)
begin
  rintros (_|i) (_|j) ⟨rfl⟩,
  { dsimp [yet_another_iso._match_1, iso.refl_hom], rw category.comp_id,
    --apply_fun AddCommGroup.adj.hom_equiv _ _,
    --simp only [AddCommGroup.adj.hom_equiv_unit],
    --have := AddCommGroup.adj.right_triangle_components,
    dsimp [evaluated_free_ExtrDisc_Cech, unsheafified_free_ExtrDiscr_Cech],
    rw if_pos (rfl : (1 : ℕ) = 0 + 1), erw category.id_comp,
    rw if_pos (rfl : (1 : ℕ) = 0 + 1), erw category.id_comp,

    --apply_fun AddCommGroup.adj.hom_equiv _ _,
    sorry
  },
  { sorry }
end

lemma free_Cech_exact (F : arrow Profinite.{u}) (hF : function.surjective F.hom) : ∀ (n : ℤ),
  is_zero $ (free_Cech F).homology n :=
begin
  dsimp only [free_Cech],
  rw chain_complex.homology_zero_iff_homology_zero,
  rw chain_complex.homology_zero_iff_map_homology_zero _
    (Condensed_ExtrSheaf_equiv Ab.{u+1}).symm,
  intros i,
  dsimp only [equivalence.symm_functor],
  let E := (_root_.homology_functor _ _ i).map_iso (free_Cech'_iso_ExtrDisc F),
  apply is_zero.of_iso _ E, clear E,
  let E := (_root_.homology_functor _ _ i).map_iso (free_ExtrDisc_Cech'_iso F),
  apply is_zero.of_iso _ E, clear E,
  dsimp only [_root_.homology_functor],
  revert i,
  apply category_theory.Sheaf.map_presheaf_to_Sheaf_homology_zero_of_homology_zero.{(u+2) u (u+1)},
  apply category_theory.homology_zero_of_eval.{(u+2) u (u+1)},
  any_goals { apply_instance },
  intros X, tactic.op_induction',
  intros i,
  let E := (_root_.homology_functor _ _ i).map_iso (yet_another_iso F X),
  apply is_zero.of_iso _ E,
  -- Now we can use the splitting similarly to arrow.conerve_to_cocomplex_homology_is_zero
  -- but we need a dual variant.
  let G := ((Profinite_to_ExtrDisc_presheaf.flip.obj (op X)).map_arrow.obj F),
  haveI : G.split,
  { suffices : function.surjective G.hom,
    { refine ⟨λ i, (this i).some, _⟩,
      ext1 i, exact (this i).some_spec },
    dsimp [G, functor.map_arrow, Profinite_to_ExtrDisc_presheaf, ulift_functor, yoneda],
    rintros ⟨e⟩,
    use ExtrDisc.lift _ hF e,
    ext1,
    dsimp,
    rw ExtrDisc.lift_lifts },
  apply arrow.nerve_to_complex_homology_is_zero AddCommGroup.free G,
  recover,
end

lemma free_Cech_kernel_SES (F : arrow Profinite.{u}) (hF : function.surjective F.hom) : ∀ n,
  short_exact (kernel.ι $ (free_Cech F).d (n+1+1) (n+1)) (delta_to_kernel _ (n+1+1) (n+1) n) :=
begin
  erw ← is_acyclic_iff_short_exact_to_cycles' (free_Cech F), exact free_Cech_exact F hF
end

variable (M : Condensed.{u} Ab.{u+1})

abbreviation HH (i : ℤ) (S : Profinite.{u}) (M : Condensed.{u} Ab.{u+1}) :=
((Ext' i).obj (op $ (CondensedSet_to_Condensed_Ab).obj $ Profinite.to_Condensed S)).obj M

def acyclic_of_exact.IH (n : ℤ) : Prop := ∀ S, ∀ i > 0, i ≤ n → is_zero (HH i S M)

/-- Consider the following commutative diagram
```
     O₀
     ↓
A₁ → B₁ → C₁ → O₁
   ↘ ↓
     B₂
     ↓  ↘
O₃ → B₃ → C₃
```
where `O₀`, `O₁`, and `O₃` are zero objects, and all sequence are exact.

Then `C₁` is also a zero object.
-/
lemma acyclic_of_exact.induction_step_aux {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  {O₀ O₁ O₃ A₁ B₁ C₁ B₂ B₃ C₃ : 𝓐}
  {α₁ : A₁ ⟶ B₁} {β₁ : B₁ ⟶ C₁} {γ₁ : C₁ ⟶ O₁} (ex₁ : exact_seq 𝓐 [α₁, β₁, γ₁])
  {d₁ : A₁ ⟶ B₂} {d₂ : B₂ ⟶ C₃}                 (exd : exact d₁ d₂)
  {b₀ : O₀ ⟶ B₁} {b₁ : B₁ ⟶ B₂} {b₂ : B₂ ⟶ B₃} (exb : exact_seq 𝓐 [b₀, b₁, b₂])
  {α₃ : O₃ ⟶ B₃} {β₃ : B₃ ⟶ C₃}                 (ex₃ : exact α₃ β₃)
  (hO₀ : is_zero O₀) (hO₁ : is_zero O₁) (hO₃ : is_zero O₃)
  (tr₁ : α₁ ≫ b₁ = d₁) (tr₂ : b₂ ≫ β₃ = d₂) :
  is_zero C₁ :=
begin
  refine (ex₁.drop 1).pair.is_zero_of_eq_zero_eq_zero
    (ex₁.pair.eq_zero_of_epi _) (hO₁.eq_of_tgt _ _),
  haveI : mono b₁ := exb.pair.mono_of_eq_zero (hO₀.eq_of_src _ _),
  haveI : mono β₃ := ex₃.mono_of_eq_zero (hO₃.eq_of_src _ _),
  let l' := abelian.is_limit_of_exact_of_mono _ _ (exb.drop 1).pair,
  let l := is_kernel_comp_mono l' β₃ tr₂.symm,
  obtain rfl :
    α₁ = kernel.lift _ _ exd.w ≫ (is_limit.cone_point_unique_up_to_iso (limit.is_limit _) l).hom,
  { erw [← cancel_mono b₁, category.assoc,
      is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_parallel_pair.zero, is_limit.fac,
      fork.of_ι_π_app, tr₁] },
  apply epi_comp
end

lemma acyclic_of_exact.induction_step_ex₁
  (F : arrow Profinite.{u})
  (h : ∀ i, is_zero (((((cosimplicial_object.augmented.whiskering _ _).obj M.val).obj
      F.augmented_cech_nerve.right_op).to_cocomplex).homology i)) :
  let C := (((cosimplicial_object.augmented.whiskering Profiniteᵒᵖ Ab).obj
    ((Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab).op ⋙ preadditive_yoneda.obj M)).obj
    F.augmented_cech_nerve.right_op).to_cocomplex
  in ∀ i, is_zero (C.homology i) :=
begin
  intros C i,
  apply is_zero.of_iso (h i),
  refine (_root_.homology_functor _ _ i).map_iso _,
  refine cosimplicial_object.augmented.cocomplex.map_iso _,
  refine iso.app (functor.map_iso _ (condensed.profinite_free_adj _)) _,
end

lemma acyclic_of_exact.induction_step_ex₂
  (F : arrow Profinite.{u})
  (h : let C := (((cosimplicial_object.augmented.whiskering Profiniteᵒᵖ Ab).obj
    ((Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab).op ⋙ preadditive_yoneda.obj M)).obj
    F.augmented_cech_nerve.right_op).to_cocomplex
    in ∀ i, is_zero (C.homology i)) :
  ∀ i, is_zero ((((preadditive_yoneda.obj M).map_homological_complex _).obj (free_Cech' F).op).homology i) :=
begin
  intro i, apply (h i).of_iso,
  refine (_root_.homology_functor _ _ _).map_iso _,
  apply acyclic_of_exact.induction_step_ex₂_aux,
end

lemma int.of_nat_add_one (i : ℕ) : int.of_nat i + 1 = int.of_nat (i+1) := rfl

lemma complex_shape.embedding.nat_down_int_down.r_int_of_nat (i : ℕ) :
  complex_shape.embedding.nat_down_int_down.r (int.of_nat i) = option.some i := rfl

-- move me
lemma cochain_complex.mono_of_is_zero_homology_0
  {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  (C : cochain_complex 𝓐 ℕ) (h : is_zero $ C.homology 0) :
  mono (C.d 0 1) :=
begin
  delta homological_complex.homology at h,
  simp only [homological_complex.d_to_eq_zero, cochain_complex.prev_nat_zero, eq_self_iff_true] at h,
  have f := homology_iso_cokernel_lift (C.d_to 0) (C.d_from 0) (by simp),
  simp only [homological_complex.d_to_eq_zero, cochain_complex.prev_nat_zero, eq_self_iff_true,
    kernel.lift_zero] at f,
  replace f := f ≪≫ limits.cokernel_zero_iso_target,
  simp_rw [C.d_from_eq (show (complex_shape.up ℕ).rel 0 1, by simp)] at f h,
  exact preadditive.mono_of_kernel_zero (is_zero.eq_of_src (is_zero.of_iso h
    (f ≪≫ (kernel_comp_mono _ _)).symm) _ _)
end

lemma acyclic_of_exact.induction_step_ex₃
  (F : arrow Profinite.{u}) (i : ℤ)
  (h : ∀ i, is_zero ((((preadditive_yoneda.obj M).map_homological_complex _).obj (free_Cech' F).op).homology i)) :
  exact ((preadditive_yoneda.obj M).map $ ((free_Cech F).d (i+1) i).op)
    ((preadditive_yoneda.obj M).map $ ((free_Cech F).d (i+1+1) (i+1)).op) :=
begin
  rcases i with (i|i),
  { delta free_Cech,
    dsimp only [homological_complex.embed, homological_complex.embed.obj],
    rw [int.of_nat_add_one, int.of_nat_add_one],
    erw [complex_shape.embedding.nat_down_int_down.r_int_of_nat],
    erw [complex_shape.embedding.nat_down_int_down.r_int_of_nat],
    erw [complex_shape.embedding.nat_down_int_down.r_int_of_nat],
    dsimp only [homological_complex.embed.d],
    refine exact_of_homology_is_zero ((h (i+1)).of_iso $ _),
    { rw [← functor.map_comp, ← op_comp, homological_complex.d_comp_d, op_zero, functor.map_zero] },
    clear h,
    refine _ ≪≫ (homology_iso _ i (i+1) (i+1+1) _ _).symm,
    swap, { dsimp, refl }, swap, { dsimp, refl },
    refl, },
  { have aux : (preadditive_yoneda.obj M).map ((free_Cech F).d (-[1+ i] + 1) -[1+ i]).op = 0,
    { cases i; erw [op_zero, functor.map_zero], },
    rw [aux], clear aux, apply_with exact_zero_left_of_mono {instances:=ff}, { apply_instance },
    cases i,
    { exact cochain_complex.mono_of_is_zero_homology_0 _ (h 0), },
    { apply mono_of_is_zero_object,
      rw [is_zero_iff_id_eq_zero, ← category_theory.functor.map_id,
        is_zero_iff_id_eq_zero.mp, functor.map_zero],
      refine (is_zero_zero _).op, } },
end

lemma acyclic_of_exact.induction_step_ex₄
  (F : arrow Profinite.{u}) (i : ℤ)
  (h : exact ((preadditive_yoneda.obj M).map $ ((free_Cech F).d (i+1) i).op)
    ((preadditive_yoneda.obj M).map $ ((free_Cech F).d (i+1+1) (i+1)).op)) :
  exact (((Ext' 0).flip.obj M).map $ ((free_Cech F).d (i+1) i).op)
        (((Ext' 0).flip.obj M).map $ ((free_Cech F).d (i+1+1) (i+1)).op) :=
begin
  let e := (bounded_derived_category.Ext'_zero_flip_iso _ M).symm,
  apply preadditive.exact_of_iso_of_exact' _ _ _ _ (e.app _) (e.app _) (e.app _) _ _ h,
  { simp only [nat_iso.app_hom, nat_trans.naturality], },
  { simp only [nat_iso.app_hom, nat_trans.naturality], }
end

lemma acyclic_of_exact.induction_step_ex
  (F : arrow Profinite.{u}) (surj : function.surjective F.hom)
  (h : ∀ i, is_zero (((((cosimplicial_object.augmented.whiskering _ _).obj M.val).obj
      F.augmented_cech_nerve.right_op).to_cocomplex).homology i))
  (i : ℤ) :
  exact (((Ext' 0).flip.obj M).map $ ((free_Cech F).d (i+1) i).op)
        (((Ext' 0).flip.obj M).map $ ((free_Cech F).d (i+1+1) (i+1)).op) :=
begin
  apply acyclic_of_exact.induction_step_ex₄,
  apply acyclic_of_exact.induction_step_ex₃,
  apply acyclic_of_exact.induction_step_ex₂,
  apply acyclic_of_exact.induction_step_ex₁ _ F h,
end

lemma acyclic_of_exact.induction_step
  (h : ∀ (F : arrow Profinite.{u}) (surj : function.surjective F.hom),
    ∀ i, is_zero (((((cosimplicial_object.augmented.whiskering _ _).obj M.val).obj
      F.augmented_cech_nerve.right_op).to_cocomplex).homology i))
  (n : ℤ) (ih : acyclic_of_exact.IH M n) :
  acyclic_of_exact.IH M (n+1) :=
begin
  intros S i h1 h2,
  rw [le_iff_eq_or_lt, or_comm, int.lt_add_one_iff] at h2,
  cases h2 with h2 h2, { exact ih S i h1 h2 },
  subst i,
  let F := arrow.mk S.projective_presentation.f,
  have hF : function.surjective F.hom,
  { rw ← Profinite.epi_iff_surjective, apply projective_presentation.epi },
  let E := λ i, (Ext' i).flip.obj M,
  have ih' : ∀ (i j : ℤ) (h0i : 0 < i) (hin : i ≤ n),
    is_zero ((E i).obj (op ((free_Cech F).X j))),
  { intros i j h0i hin,
    cases j with j j,
    { cases j; exact ih _ _ h0i hin, },
    { apply bounded_derived_category.Ext'_zero_left_is_zero,
      exact (is_zero_zero _).op, } },
  let K := λ i, kernel ((free_Cech F).d (i + 1) i),
  have LES := λ i j, (free_Cech_kernel_SES F hF i).Ext'_five_term_exact_seq M j,
  have H1 : ∀ i > 0, is_zero ((E i).obj (op ((free_Cech F).X 1))),
  { intros i hi,
    apply bounded_derived_category.Ext'_is_zero_of_projective _ _ _ _ hi,
    apply_with Condensed_Ab.free.category_theory.projective {instances:=ff},
    rw [simplicial_object.augmented.drop_obj, arrow.augmented_cech_nerve_left],
    apply projective.of_iso (arrow.cech_nerve_obj_0 F).symm,
    apply projective_presentation.projective, },
  have aux0 : ∀ (i : ℤ) (h0i : 0 < i+1) (H : is_zero ((E i).obj (op $ K 0))),
    is_zero ((E (i+1)).obj (op $ K (-1))),
  { intros i h0i H,
    refine is_zero_of_exact_is_zero_is_zero _ _ ((LES (-1) i).drop 2).pair H (H1 _ h0i), },
  have aux : ∀ (i j : ℤ) (h0i : 0 < i+1) (hi : i+1 ≤ n) (H : is_zero ((E i).obj (op $ K (j+1)))),
    is_zero ((E (i+1)).obj (op $ K j)),
  { intros i j h0i hi H,
    refine is_zero_of_exact_is_zero_is_zero _ _ ((LES j i).drop 2).pair H _,
    refine ih' _ _ h0i hi },
  suffices : ∀ i j, 0 < i → -1 ≤ j → i + j = n → is_zero ((E i).obj (op $ K j)),
  { refine is_zero_of_exact_is_zero_is_zero _ _ (LES (-2) (n+1)).pair _ _; clear LES,
    { apply bounded_derived_category.Ext'_zero_left_is_zero,
      refine (is_zero_of_mono (kernel.ι _) _).op, refine is_zero_zero _, },
    { refine this (n+1) (-1) h1 le_rfl _, rw [← sub_eq_add_neg, add_sub_cancel] } },
  obtain ⟨n, rfl⟩ : ∃ k, k+1 = n := ⟨n-1, sub_add_cancel _ _⟩,
  suffices : is_zero ((E 1).obj (op $ K n)),
  { intro i,
    apply int.induction_on' i 1; clear i,
    { intros j h0i hj hijn, rw [add_comm (1:ℤ), add_left_inj] at hijn, subst j, exact this },
    { intros i hi IH j hi' hj hijn,
      rw le_iff_eq_or_lt at hj, cases hj with hj hj,
      { subst j, apply aux0 _ hi', apply IH; linarith only [hi, hijn] },
      { apply aux _ _ hi' _ (IH _ _ _ _); linarith only [hi, hijn, hj], } },
    { intros i hi IH j hi', exfalso, linarith only [hi, hi'] } },
  clear aux0 aux,
  have aux := λ i, ((LES i (-1)).drop 2).pair.cons (LES i 0),
  have exd := acyclic_of_exact.induction_step_ex M F hF (h F hF) (n+1+1),
  apply acyclic_of_exact.induction_step_aux
    ((LES n 0).drop 1) exd ((aux (n+1)).extract 0 3) (aux (n+1+1)).pair; clear LES aux exd,
  { apply Ext'_is_zero_of_neg, dec_trivial },
  { obtain (rfl|hn) : n = -1 ∨ 1 ≤ n + 1,
    { rw [or_iff_not_imp_right], intro h2, linarith only [h1, h2] },
    { exact H1 _ zero_lt_one },
    { exact ih' _ _ zero_lt_one hn } },
  { apply Ext'_is_zero_of_neg, dec_trivial },
  { conv_rhs { rw [← delta_to_kernel_ι _ _ _ (n+1), op_comp, functor.map_comp] }, refl },
  { conv_rhs { rw [← delta_to_kernel_ι _ _ _ (n+1+1), op_comp, functor.map_comp] }, refl },
end

lemma acyclic_of_exact
  (h : ∀ (F : arrow Profinite.{u}) (surj : function.surjective F.hom),
    ∀ i, is_zero
    (((((cosimplicial_object.augmented.whiskering _ _).obj M.val).obj
      F.augmented_cech_nerve.right_op).to_cocomplex).homology i))
  (S : Profinite.{u}) :
  ∀ i > 0, is_zero (HH i S M)  :=
begin
  intros i hi,
  suffices : acyclic_of_exact.IH M i,
  { apply this S i hi le_rfl, },
  apply int.induction_on' i 0; clear hi i S,
  { intros S i h1 h2, exfalso, exact h2.not_lt h1 },
  { intros k hk, apply acyclic_of_exact.induction_step M h, },
  { rintros k hk aux S i h1 h2, exfalso, linarith only [hk, h1, h2] }
end

end condensed
