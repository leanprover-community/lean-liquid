import category_theory.preadditive.additive_functor
import category_theory.limits.preserves.shapes.biproducts

import for_mathlib.derived.les2
import for_mathlib.derived.les_facts
import for_mathlib.salamander
.

noncomputable theory

open category_theory category_theory.limits opposite
open homotopy_category (hiding single)
open bounded_homotopy_category


section

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]

def delta_to_kernel (C : cochain_complex 𝓐 ℤ) (i : ℤ) :
  C.X i ⟶ kernel (C.d (i+1) (i+1+1)) :=
factor_thru_image _ ≫ image_to_kernel' (C.d i (i+1)) _ (C.d_comp_d _ _ _)

lemma short_exact_comp_iso {A B C D : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (hh : is_iso h) :
  short_exact f (g ≫ h) ↔ short_exact f g :=
begin
  split; intro H,
  { haveI : mono f := H.mono,
    haveI : epi g,
    { haveI := H.epi, have := epi_comp (g ≫ h) (inv h), simpa only [category.assoc, is_iso.hom_inv_id, category.comp_id] },
    refine ⟨_⟩, have := H.exact, rwa exact_comp_iso at this, },
  { haveI : mono f := H.mono,
    haveI : epi g := H.epi,
    haveI : epi (g ≫ h) := epi_comp g h,
    refine ⟨_⟩, have := H.exact, rwa exact_comp_iso }
end

lemma homology_is_zero_iff_image_to_kernel'_is_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  is_zero (homology f g w) ↔ is_iso (image_to_kernel' f g w) :=
sorry

lemma short_exact_kernel_factor_thru_image {A B : 𝓐} (f : A ⟶ B) :
  short_exact (kernel.ι f) (factor_thru_image f) :=
sorry

lemma is_acyclic_def
  (C : homotopy_category 𝓐 (complex_shape.up ℤ)) :
  is_acyclic C ↔ (∀ i, is_zero (C.as.homology i)) :=
begin
  split,
  { apply is_acyclic.cond },
  { apply is_acyclic.mk }
end

lemma is_acyclic_iff_short_exact_to_cycles
  (C : homotopy_category 𝓐 (complex_shape.up ℤ)) :
  is_acyclic C ↔
  (∀ i, short_exact (kernel.ι (C.as.d i (i+1))) (delta_to_kernel C.as i)) :=
begin
  rw is_acyclic_def,
  symmetry,
  apply (equiv.add_right (1 : ℤ)).forall_congr,
  intro i,
  let e := (homology_iso C.as i (i+1) (i+1+1) rfl rfl),
  dsimp [delta_to_kernel] at e ⊢,
  rw [e.is_zero_iff, homology_is_zero_iff_image_to_kernel'_is_iso],
  split,
  { intro h, sorry },
  { intro h, rw short_exact_comp_iso _ _ _ h, apply short_exact_kernel_factor_thru_image }
end


end

variables {𝓐 𝓑 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
variables [category 𝓑] [abelian 𝓑] [enough_projectives 𝓑]

variables (C : cochain_complex 𝓐 ℤ)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj C)]

def category_theory.functor.single (F : bounded_homotopy_category 𝓐 ⥤ 𝓑) (i : ℤ) : 𝓐 ⥤ 𝓑 :=
bounded_homotopy_category.single _ i ⋙ F

-- move me
lemma category_theory.limits.is_zero.biprod {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  {X Y : 𝓐} (hX : is_zero X) (hY : is_zero Y) :
  is_zero (X ⊞ Y) :=
begin
  rw is_zero_iff_id_eq_zero at hX hY ⊢,
  ext; simp [hX, hY],
end

instance category_theory.limits.preserves_binary_biproduct_of_additive
  {𝓐 𝓑 : Type*} [category 𝓐] [category 𝓑] [abelian 𝓐] [abelian 𝓑]
  (F : 𝓐 ⥤ 𝓑) [functor.additive F] (X Y : 𝓐) :
  preserves_binary_biproduct X Y F :=
preserves_binary_biproduct_of_preserves_biproduct _ _ _

-- move me
@[simp] lemma category_theory.op_neg {𝓐 : Type*} [category 𝓐] [preadditive 𝓐]
  {X Y : 𝓐} (f : X ⟶ Y) : (-f).op = - f.op := rfl

lemma acyclic_left_of_short_exact (B : 𝓐) {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : short_exact f g)
  (hY : ∀ i > 0, is_zero (((Ext' i).obj (op $ Y)).obj B))
  (hZ : ∀ i > 0, is_zero (((Ext' i).obj (op $ Z)).obj B)) :
  ∀ i > 0, is_zero (((Ext' i).obj (op $ X)).obj B) :=
begin
  intros i hi,
  let f' := (homological_complex.single _ (complex_shape.up ℤ) (0:ℤ)).map f,
  let g' := (homological_complex.single _ (complex_shape.up ℤ) (0:ℤ)).map g,
  let B' := (bounded_homotopy_category.single _ 0).obj B,
  have Hfg : ∀ (i : ℤ), short_exact (f'.f i) (g'.f i),
  { intro i, dsimp, by_cases hi : i = 0,
    { subst i, dsimp, simp only [eq_self_iff_true, category.comp_id, category.id_comp, if_true, hfg] },
    { rw [dif_neg hi, dif_neg hi, if_neg hi, if_neg hi, if_neg hi],
      refine ⟨exact_of_zero _ _⟩, } },
  have := Ext_five_term_exact_seq' f' g' i B' Hfg,
  refine (this.drop 1).pair.is_zero_of_is_zero_is_zero (hY _ hi) (hZ _ _),
  transitivity i, { exact lt_add_one i }, { exact hi }
end

lemma map_is_acyclic_of_acyclic
  [is_acyclic ((homotopy_category.quotient _ _).obj C)]
  (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B)) :
  is_acyclic (((preadditive_yoneda.obj B).right_op.map_homotopy_category _).obj ((homotopy_category.quotient _ _).obj C)) :=
begin
  rw is_acyclic_iff_short_exact_to_cycles,
  obtain ⟨a, ha⟩ := is_bounded_above.cond ((quotient 𝓐 _).obj C),
  intro i,
  sorry
end

lemma acyclic_of_projective (P B : 𝓐) [projective P] (i : ℤ) (hi : 0 < i) :
  is_zero (((Ext' i).obj (op P)).obj B) :=
begin
  rw (Ext'_iso (op P) B i _ (𝟙 _) _).is_zero_iff,
  { rcases i with ((_|i)|i),
    { exfalso, revert hi, dec_trivial },
    swap, { exfalso, revert hi, dec_trivial },
    refine is_zero.homology_is_zero _ _ _ _,
    apply AddCommGroup.is_zero_of_eq,
    intros,
    apply is_zero.eq_of_src,
    apply is_zero_zero, },
  { refine ⟨_, _, _⟩,
    { rintro (_|n), { assumption }, { dsimp, apply_instance } },
    { exact exact_zero_mono (𝟙 P) },
    { rintro (_|n); exact exact_of_zero 0 0 } }
end

def Ext_compute_with_acyclic
  (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B))
  (i : ℤ) :
  ((Ext i).obj (op $ of' C)).obj ((single _ 0).obj B) ≅
  unop ((((preadditive_yoneda.obj B).right_op.map_homological_complex _).obj C).homology (-i)) :=
begin
  let P := (of' C).replace,
  let π : P ⟶ of' C := (of' C).π,
  let B' := (single _ 0).obj B,
  let HomB := (preadditive_yoneda.obj B).right_op.map_homological_complex (complex_shape.up ℤ),
  let f := HomB.map π.out,
  let fq := (homotopy_category.quotient _ _).map f,
  suffices hf : is_quasi_iso fq,
  { resetI,
    let e := as_iso ((homotopy_category.homology_functor Abᵒᵖ _ (-i)).map fq),
    let e' := e.symm.unop,
    refine _ ≪≫ e',
    refine _ ≪≫ (homology_iso _ (-i-1) (-i) (-i+1) _ _).unop,
    rotate, { dsimp, apply sub_add_cancel }, { dsimp, refl },
    refine _ ≪≫ (LBC.homology_unop_iso _ _ _).unop,
    refine (preadditive_yoneda.map_iso _).app (op P) ≪≫ _,
    { exact (single 𝓐 (-i)).obj B },
    { exact (shift_single_iso 0 i).app B ≪≫ eq_to_iso (by rw zero_sub) },
    refine hom_single_iso _ _ _ ≪≫ _,
    refine (homology_iso _ (-i+1) (-i) (-i-1) _ _),
    { dsimp, refl }, { dsimp, apply sub_add_cancel }, },
  have := cone_triangleₕ_mem_distinguished_triangles _ _ f,
  replace := is_quasi_iso_iff_is_acyclic _ this,
  dsimp [homological_complex.cone.triangleₕ] at this,
  rw this, clear this i,
  constructor,
  intro i, obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩,
  refine is_zero.of_iso _ (homology_iso _ i (i+1) (i+1+1) _ _),
  rotate, { dsimp, refl }, { dsimp, refl },
  apply exact.homology_is_zero _,
  dsimp only [homotopy_category.quotient, quotient.functor_obj_as, homological_complex.cone_d],
  have hπ : is_quasi_iso π, { dsimp [π], apply_instance },
  have := cone_triangleₕ_mem_distinguished_triangles _ _ π.out,
  replace := is_quasi_iso_iff_is_acyclic _ this,
  dsimp [homological_complex.cone.triangleₕ] at this,
  simp only [quotient_map_out] at this,
  replace := this.mp _,
  swap, { convert hπ using 1, generalize : P.val = X, cases X, refl, },
  haveI preaux : ((quotient 𝓐 (complex_shape.up ℤ)).obj (homological_complex.cone (quot.out π))).is_bounded_above,
  { constructor,
    obtain ⟨a, ha⟩ := is_bounded_above.cond ((quotient 𝓐 (complex_shape.up ℤ)).obj C),
    obtain ⟨b, hb⟩ := is_bounded_above.cond P.val,
    refine ⟨max a b, _⟩,
    intros k hk,
    refine category_theory.limits.is_zero.biprod _ _,
    { apply hb, refine (le_max_right _ _).trans (hk.trans (lt_add_one _).le) },
    { apply ha, exact (le_max_left _ _).trans hk, } },
  have aux := @map_is_acyclic_of_acyclic _ _ _ _ _ _ this B _,
  { replace := (@is_acyclic.cond _ _ _ _ aux (i+1)).of_iso (homology_iso _ i (i+1) (i+1+1) _ _).symm,
    rotate, { dsimp, refl }, { dsimp, refl },
    dsimp only [homotopy_category.quotient, quotient.functor_obj_as, homological_complex.cone_d,
      functor.map_homotopy_category_obj, functor.map_homological_complex_obj_d] at this,
    replace := exact_of_homology_is_zero this,
    let e := functor.map_biprod (preadditive_yoneda.obj B).right_op,
    refine preadditive.exact_of_iso_of_exact' _ _ _ _ (e _ _) (e _ _) (e _ _) _ _ this;
    dsimp only [e, functor.map_biprod_hom],
    all_goals
    { ext,
      { simp only [category.assoc, functor.right_op_map, homological_complex.cone.d, biprod.lift_fst,
          eq_self_iff_true, functor.map_homological_complex_obj_d, functor.right_op_map,
          homological_complex.X_eq_to_iso_refl, category.comp_id, dite_eq_ite, if_true,
          biprod.lift_fst, biprod.lift_desc, preadditive.comp_neg, comp_zero, add_zero],
        simp only [functor.map_homological_complex_obj_d, functor.right_op_map, functor.comp_map,
          biprod.lift_desc, preadditive.comp_neg, comp_zero, add_zero,
          ← op_comp, ← category_theory.functor.map_comp, biprod.lift_fst],
        simp only [biprod.desc_eq, comp_zero, add_zero, preadditive.comp_neg,
          category_theory.op_neg, functor.map_neg], },
      { simp only [category.assoc, functor.right_op_map, homological_complex.cone.d, biprod.lift_snd,
          eq_self_iff_true, functor.map_homological_complex_obj_d, functor.right_op_map,
          functor.map_homological_complex_map_f, homological_complex.X_eq_to_iso_refl,
          category.comp_id, dite_eq_ite, if_true, biprod.lift_snd, biprod.lift_desc],
        simp only [functor.map_homological_complex_obj_d, functor.right_op_map, functor.comp_map,
          biprod.lift_desc, preadditive.comp_neg, comp_zero, add_zero,
          ← op_comp, ← category_theory.functor.map_comp, biprod.lift_snd],
        simp only [biprod.desc_eq, op_add, functor.map_neg, functor.map_add] } } },
  { clear i, intros k i hi,
    let e := functor.map_biprod ((Ext' i).flip.obj B).right_op
      (P.val.as.X (k + 1)) ((of' C).val.as.X k),
    refine is_zero.of_iso (is_zero.unop _) e.symm.unop,
    refine category_theory.limits.is_zero.biprod _ _,
    { simp only [functor.right_op_obj, functor.flip_obj_obj, is_zero_op],
      exact acyclic_of_projective (P.val.as.X (k + 1)) B i hi, },
    { exact (hC k _ hi).op, }, }
end
