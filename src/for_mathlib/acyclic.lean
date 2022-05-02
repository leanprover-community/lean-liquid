import for_mathlib.derived.les2
import for_mathlib.derived.les_facts
.

noncomputable theory

open category_theory category_theory.limits opposite
open homotopy_category (hiding single)
open bounded_homotopy_category

variables {𝓐 𝓑 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
variables [category 𝓑] [abelian 𝓑] [enough_projectives 𝓑]

variables (C : cochain_complex 𝓐 ℤ)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj C)]

def category_theory.functor.single (F : bounded_homotopy_category 𝓐 ⥤ 𝓑) (i : ℤ) : 𝓐 ⥤ 𝓑 :=
bounded_homotopy_category.single _ i ⋙ F

-- def compute_with_acyclic
--   (F : bounded_homotopy_category 𝓐 ⥤ 𝓑) (C : cochain_complex 𝓐 ℤ)
--   [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj C)]
--   (hC : ∀ k, ∀ i > 0, is_zero ((F.single (-i)).obj (C.X k)))
--   (i : ℤ) :
--   F.obj (of' C⟦-i⟧) ≅
--   unop ((((preadditive_yoneda.obj B).right_op.map_homological_complex _).obj C).homology i) :=

-- #check @category_theory.quotient

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
sorry

-- move me
@[simp] lemma category_theory.op_neg {𝓐 : Type*} [category 𝓐] [preadditive 𝓐]
  {X Y : 𝓐} (f : X ⟶ Y) : (-f).op = - f.op := rfl

def map_is_acyclic_of_acyclic
  [is_acyclic ((homotopy_category.quotient _ _).obj C)]
  (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B)) :
  is_acyclic (((preadditive_yoneda.obj B).right_op.map_homotopy_category _).obj ((homotopy_category.quotient _ _).obj C)) :=
begin
  sorry
end

def Ext_compute_with_acyclic
  (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B))
  (i : ℤ) :
  ((Ext i).obj (op $ of' C)).obj ((single _ 0).obj B) ≅
  unop ((((preadditive_yoneda.obj B).right_op.map_homological_complex _).obj C).homology i) :=
begin
  let P := (of' C).replace,
  let π : P ⟶ of' C := (of' C).π,
  let B' := (single _ 0).obj B,
  let HomB := (preadditive_yoneda.obj B).right_op.map_homological_complex (complex_shape.up ℤ),
  let f := HomB.map π.out,
  let fq := (homotopy_category.quotient _ _).map f,
  suffices hf : is_quasi_iso fq,
  { resetI,
    let e := as_iso ((homotopy_category.homology_functor Abᵒᵖ _ i).map fq),
    let e' := e.symm.unop,
    refine _ ≪≫ e',
    -- currently there are some `op`s in the wrong places
    -- so this is provable, but requires identifying the `op` of homology with the homology of `op`s
    -- a similar isom is proved in `salamander.lean`, I think
    sorry },
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
    { sorry },
    { exact (hC k _ hi).op, }, }
end
