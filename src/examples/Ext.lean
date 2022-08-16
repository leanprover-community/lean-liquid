import challenge_notations
import challenge_prerequisites
import for_mathlib.universal_delta_functor.Ext

/-!

This file shows that `Ext` is a universal δ-functor
and performs the computation `Ext^1(ℤ/nℤ, ℤ/nℤ) = ℤ/nℤ`.

-/

noncomputable theory

open_locale liquid_tensor_experiment

open category_theory category_theory.limits opposite
open bounded_homotopy_category bounded_derived_category

section Ext

universes v u
-- Let's work with an abelian category which has enough projectives.
variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐] [enough_projectives 𝓐]

/-- This is the (contravariant) delta functor `X ↦ Ext^*(X,B)`. -/
example (Y : 𝓐) : 𝓐ᵒᵖ ⥤δ Ab.{v} := Ext_δ_functor 𝓐 Y

/-- The `n-th` component of this delta functor. -/
example (n : ℕ) (Y : 𝓐) : 𝓐ᵒᵖ ⥤ Ab.{v} := Ext_δ_functor 𝓐 Y n
example (n : ℕ) (X Y : 𝓐) :
  (Ext_δ_functor 𝓐 Y n) (op X) = ((Ext' n) (op X)) Y :=
rfl

/- The functor from `𝓐` to the bounded above homotopy category,
sending `X` to `X[0]`. -/
example : 𝓐 ⥤ bounded_homotopy_category 𝓐 :=
single _ 0

/- We introduced a coercion to simplify the notation. -/
example (X : 𝓐) : bounded_homotopy_category 𝓐 := X
example (X : 𝓐) : (X : bounded_homotopy_category 𝓐) = (single _ 0) X := rfl

/--
`Ext' n (X,B)` is definitionally equal to `Ext n (X, B)`.
We have to manually tell Lean that a coercion is involved in this case using `↑`.
-/
example (n : ℕ) (X Y : 𝓐) :
  (Ext' n (op X)) Y =
  (Ext n (op ↑X)) ↑Y := rfl

/-- `Ext' 0 (-, B) ≅ Hom(-,B)` -/
example (X Y : 𝓐) : (Ext' 0 (op X)) Y ≅ AddCommGroup.of (X ⟶ Y) :=
(Ext'_zero_flip_iso _ _).app _

/-- Any natural transformation `Hom(-,B) ⟶ F 0` to the zeroth-component of some
delta functor `F` extends in a unique way to a morphism of delta functors
`Ext_δ_functor A B ⟶ F`.

Note that `Ext' 0 (X,B)` is not defeq to `Hom(X,B)`, so we must compose with the isomorphism
`Ext'_zero_flip_iso` that was mentioned in the previous example.
-/
theorem Ext_δ_functor_is_universal_for_Hom (Y : 𝓐) (F : 𝓐ᵒᵖ ⥤δ Ab.{v})
  (e0 : preadditive_yoneda Y ⟶ F 0) :
  ∃! (e : Ext_δ_functor 𝓐 Y ⟶ F),
  e0 = (Ext'_zero_flip_iso _ _).inv ≫ (e : Ext_δ_functor 𝓐 Y ⟶ F) 0 :=
begin
  let e0' : Ext_δ_functor 𝓐 Y 0 ⟶ F 0 := (Ext'_zero_flip_iso _ _).hom ≫ e0,
  obtain ⟨e,he1,he2⟩ := delta_functor.universal.cond F e0',
  refine ⟨e,_,_⟩,
  { dsimp, simp only [e0', he1, iso.inv_hom_id_assoc], },
  { intros η hη, specialize he2 η,
    apply he2, rw iso.eq_inv_comp at hη,
    exact hη.symm },
end

end Ext

namespace AddCommGroup

/-- An explicit computation: `Ext^1(ℤ/n,ℤ/n) = ℤ/n`. -/
example (n : ℕ) (hn : n ≠ 0) :
  (Ext' 1 (op $ of $ zmod n)).obj (of $ zmod n) ≅ of (zmod n) :=
begin
  refine Ext'_iso (op $ of $ zmod n) (of $ zmod n) 1 (zmod_resolution n) (zmod_resolution_pi n)
    (zmod_resolution_is_resolution n hn) ≪≫
      (category_theory.homology_iso _ 0 (-1) (-2) rfl rfl) ≪≫ _,
  refine (AddCommGroup.homology_iso _ _ _) ≪≫ _,
  refine add_equiv_iso_AddCommGroup_iso.hom _,
  refine add_equiv.surjective_congr _ (quotient_add_group.mk' _) (add_monoid_hom.id _)
    (quot.mk_surjective _) function.surjective_id _,
  refine (add_equiv.add_subgroup_congr _).trans _,
  { exact ⊤ },
  { convert add_monoid_hom.ker_zero using 2,
    refine is_zero.eq_of_tgt _ _ _,
    refine AddCommGroup.is_zero_of_eq _ _,
    intros f g,
    apply category_theory.limits.has_zero_object.from_zero_ext, },
  { refine (add_subgroup.equiv_top _).symm.trans (zmultiples_add_hom _).symm, },
  { simp only [add_monoid_hom.ker_zero, quotient_add_group.ker_mk,
     functor.map_homological_complex_obj_d, homological_complex.op_d],
    ext ⟨f, hf⟩,
    simp only [add_subgroup.mem_comap, add_equiv.coe_to_add_monoid_hom, add_equiv.coe_trans,
      function.comp_app, zmultiples_add_hom_symm_apply, add_subgroup.coe_subtype,
      add_subgroup.coe_mk, add_monoid_hom.mem_range],
    simp only [add_subgroup.equiv_top_symm_apply, add_monoid_hom.mem_ker],
    dsimp [add_equiv.add_subgroup_congr, zmod_resolution],
    split,
    { intro hf1, refine ⟨0, comp_zero.trans _⟩, ext1, exact hf1.symm },
    { intro H, cases H with g hg, rw [← hg, coe_comp],
      convert g.map_nsmul _ _ using 1,
      simp only [eq_to_hom_refl, id_apply, zmod.nsmul_eq_zero] } }
end

end AddCommGroup
