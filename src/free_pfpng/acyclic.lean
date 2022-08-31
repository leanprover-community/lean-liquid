import free_pfpng.main
import condensed.acyclic
import prop819
import locally_constant.completion
.

noncomputable theory

universes u

open category_theory category_theory.limits opposite ProFiltPseuNormGrp₁
open function (surjective)
open_locale nnreal

variables (S : Profinite.{u})
variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]

set_option pp.universes true

namespace cosimplicial_object

variables {C D E : Type*} [category C] [category D] [category E]
variables (F : C ⥤ D) (G : D ⥤ E)

@[simps]
def whiskering_comp :
  (cosimplicial_object.whiskering C E).obj (F ⋙ G) ≅
  (cosimplicial_object.whiskering C D).obj F ⋙
  (cosimplicial_object.whiskering D E).obj G :=
nat_iso.of_components
  (λ X, (nat_iso.of_components
    (λ n, iso.refl _) $
    by { intros, dsimp, simp only [category.comp_id, category.id_comp] })) $
  by { intros, ext, dsimp, simp only [category.comp_id, category.id_comp] }

namespace augmented

def whiskering_comp :
  (cosimplicial_object.augmented.whiskering C E).obj (F ⋙ G) ≅
  (cosimplicial_object.augmented.whiskering C D).obj F ⋙
  (cosimplicial_object.augmented.whiskering D E).obj G :=
nat_iso.of_components
  (λ X, comma.iso_mk (iso.refl _) ((cosimplicial_object.whiskering_comp F G).app _)
    begin
      ext,
      dsimp,
      simp only [iso.refl_hom, category_theory.functor.map_id, category.id_comp,
        iso.app_hom, functor.id_map, category.comp_id],
    end)
  begin
    intros, ext; dsimp;
    simp only [iso.refl_hom, category_theory.functor.map_id, category.id_comp,
      iso.app_hom, functor.id_map, category.comp_id],
  end
.

-- move me
attribute [simps obj map] cosimplicial_object.augmented.cocomplex

def cocomplex_whiskering_additive [preadditive C] [preadditive D] [F.additive] :
  (cosimplicial_object.augmented.whiskering C D).obj F ⋙
  cosimplicial_object.augmented.cocomplex ≅
  cosimplicial_object.augmented.cocomplex ⋙ F.map_homological_complex _ :=
nat_iso.of_components
  (λ X, homological_complex.hom.iso_of_components
    (λ i, by { cases i; exact iso.refl _, })
    begin
      rintro i j (rfl : i + 1 = j), cases i,
      { dsimp, rw [category.id_comp, category.comp_id, if_pos rfl, if_pos rfl,
          category.comp_id, category.comp_id],
        delta cosimplicial_object.augmented.to_cocomplex_d,
        dsimp, simp only [category.id_comp], },
      { dsimp, rw [category.id_comp, category.comp_id, if_pos rfl, if_pos rfl,
          category.comp_id, category.comp_id],
        delta cosimplicial_object.augmented.to_cocomplex_d cosimplicial_object.coboundary id_rhs,
        dsimp, simp only [← functor.map_add_hom_apply, map_sum, map_zsmul], refl }
    end)
  begin
    intros, ext n, dsimp, cases n;
    { dsimp, rw [category.id_comp, category.comp_id], refl, },
  end
.

end augmented
end cosimplicial_object

section
universe v
-- move me
instance Ab.ulift_additive : Ab.ulift.{u v}.additive := {}
end

lemma free_acyclic_aux (F : arrow Profinite) (hF : surjective (F.hom)) (i : ℕ) :
    is_zero ((((cosimplicial_object.augmented.whiskering Profiniteᵒᵖ Ab).obj
      (LCC V ⋙ Ab.ulift.{u+1})).obj F.augmented_cech_nerve.right_op).to_cocomplex.homology i) :=
begin
  let U := (forget₂.{u+1 u+1 u u u} SemiNormedGroup.{u} Ab.{u} ⋙ Ab.ulift.{u+1 u}),
  show is_zero (homological_complex.homology.{u+1 u+2 0}
    (((cosimplicial_object.augmented.whiskering.{u u+1 u+1 u+2} Profinite.{u}ᵒᵖ Ab.{u+1}).obj
      (SemiNormedGroup.LCC.{u u}.obj V ⋙ U)).obj F.augmented_cech_nerve.right_op).to_cocomplex i),
  rw [← homology_functor_obj, ← category_theory.cosimplicial_object.augmented.cocomplex_obj],
  let e1 := (homology_functor _ (complex_shape.up.{0} ℕ) i).map_iso
    (cosimplicial_object.augmented.cocomplex.map_iso
    ((cosimplicial_object.augmented.whiskering_comp _ U).app
    F.augmented_cech_nerve.right_op)),
  refine is_zero_of_iso_of_zero _ e1.symm,
  let e2 := (homology_functor Ab (complex_shape.up.{0} ℕ) i).map_iso
    ((cosimplicial_object.augmented.cocomplex_whiskering_additive U).app _),
  refine is_zero_of_iso_of_zero _ e2.symm,
  clear e1 e2,
  let C :=
    (U.map_homological_complex (complex_shape.up.{0} ℕ)).obj
    (((cosimplicial_object.augmented.whiskering Profinite.{u}ᵒᵖ _).obj
      (SemiNormedGroup.LCC.{u u}.obj V)).obj
      F.augmented_cech_nerve.right_op).to_cocomplex,
  show is_zero (C.homology i),
  cases i,
  { apply exact.homology_is_zero,
    rw [AddCommGroup.exact_iff', homological_complex.d_to_comp_d_from, eq_self_iff_true, true_and,
      homological_complex.d_to_eq_zero],
    swap, { simp only [cochain_complex.prev_nat_zero, complex_shape.up_rel,
        nat.one_ne_zero, not_false_iff], },
    intros f hf, refine ⟨0, ulift.down_injective (prop819_degree_zero F hF V f.down _).symm⟩,
    rw [add_monoid_hom.mem_ker] at hf,
    have h01 : (complex_shape.up.{0} ℕ).rel 0 1 := rfl,
    have := homological_complex.d_from_comp_X_next_iso C h01,
    rw [← iso.eq_comp_inv] at this,
    apply_fun (C.X_next_iso h01).hom at hf,
    rw [this, ← Ab.comp_apply, category.assoc, iso.inv_hom_id, category.comp_id, map_zero] at hf,
    exact congr_arg ulift.down hf, },
  { let e := (homology_iso C i (i+1) (i+2) rfl rfl),
    refine is_zero_of_iso_of_zero _ e.symm,
    apply exact.homology_is_zero,
    rw [AddCommGroup.exact_iff', homological_complex.d_comp_d, eq_self_iff_true, true_and],
    intros f hf,
    -- use `prop819` from `prop819.lean`
    obtain ⟨g, hg, -⟩ := prop819 F hF V 1 zero_lt_one f.down (congr_arg ulift.down hf),
    refine ⟨ulift.up g, ulift.down_injective hg⟩, },
end

theorem free_acyclic (i : ℤ) (hi : 0 < i) :
  is_zero (((Ext' i).obj (op ((Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab).obj S))).obj
    (Condensed.of_top_ab V)) :=
begin
  apply condensed.acyclic_of_exact _ _ _ i hi,
  intros F hF i,
  apply is_zero_of_iso_of_zero (free_acyclic_aux V F hF i),
  refine (homology_functor _ _ i).map_iso _,
  refine cosimplicial_object.augmented.cocomplex.map_iso _,
  conv_lhs { rw [← functor.flip_obj_obj] },
  conv_rhs { rw [← functor.flip_obj_obj] },
  refine functor.map_iso _ _,
  refine iso_whisker_right _ _,
  exact LCC_iso_Cond_of_top_ab V,
end

theorem free_pfpng_acyclic (i : ℤ) (hi : 0 < i) :
  is_zero (((Ext' i).obj (op ((condensify (free_pfpng_functor ⋙ PFPNG₁_to_CHFPNG₁ₑₗ)).obj S))).obj
    (Condensed.of_top_ab V)) :=
begin
  refine is_zero_of_iso_of_zero (free_acyclic S V i hi) _,
  conv { rw ← functor.flip_obj_obj, congr, skip, rw ← functor.flip_obj_obj },
  refine functor.map_iso _ (iso.app _ _).op,
  exact free_pfpng_profinite_iso
end
