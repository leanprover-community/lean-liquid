import challenge_notations
import challenge_prerequisites
import for_mathlib.universal_delta_functor.Ext

/-!

This file discusses the various Ext groups appearing in our project.
We also discuss the computation `Ext^1(ℤ/nℤ, ℤ/nℤ) = ℤ/nℤ`.

-/

noncomputable theory

open_locale liquid_tensor_experiment nnreal

open category_theory category_theory.limits opposite
open bounded_homotopy_category bounded_derived_category

section Ext

namespace liquid_tensor_experiment

/-!
The `Ext i (ℳ_{p'} S) V` which appears in the main statement of the challenge
is just an alias for `Ext' i (op (ℳ_{p'} S)) (Condensed.of_top_ab V)`.
The notation `Ext'` will be explained below, while `ℳ_{p'} S` is discussed in the file
`examples/radon_measures.lean` and `(Condensed.of_top_ab V)` is discussed in the file
`examples/pBanach.lean`.
-/
example
  (p' p : ℝ≥0) [fact (0 < p')] [fact (p' < p)] [fact (p ≤ 1)]
  (S : Profinite.{0}) (V : pBanach.{0} p) :
  ∀ i > 0,
    Ext i (ℳ_{p'} S) V =
    Ext' i (op (ℳ_{p'} S)) (Condensed.of_top_ab V) :=
by { intros, refl }

end liquid_tensor_experiment

universes v u
/-!
We fix an abelian category with enough projectives.
-/
variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐] [enough_projectives 𝓐]

/-!
The functor from `𝓐` to the bounded above homotopy category, sending `X` to `X[0]`,
is denoted by `single 𝓐 0`.
-/
example : 𝓐 ⥤ bounded_homotopy_category 𝓐 :=
single 𝓐 0

/-!
We introduced a coercion to simplify the notation.
-/
example (X : 𝓐) : bounded_homotopy_category 𝓐 := X
example (X : 𝓐) : (X : bounded_homotopy_category 𝓐) = (single _ 0) X := rfl

/-!
Our Ext functor `Ext n`, for `n : ℤ`, is defined for arbitrary objects in the bounded above
homotopy category.
It is a bifunctor which is contravariant in the first component and covariant in the second.
-/
example (n : ℤ) : (bounded_homotopy_category 𝓐)ᵒᵖ ⥤ bounded_homotopy_category 𝓐 ⥤ Ab :=
Ext n

/-!
`Ext' n (X, B)` is defined to be `Ext n (X, B)`, modulo the coercion mentioned above.
We have to manually tell Lean that a coercion is involved in this case using `↑`.
-/
example (n : ℕ) (X Y : 𝓐) :
  Ext' n (op X) Y =
  Ext n (op ↑X) ↑Y :=
rfl

/-!
The `Ext' n` can be assembled into a δ-functor, which is denoted `Ext_δ_functor 𝓐 Y`.
To be precise, this is considering `Ext' n (X, Y)` as functors in `X`, with `Y` fixed.
-/
example (Y : 𝓐) : 𝓐ᵒᵖ ⥤δ Ab.{v} := Ext_δ_functor 𝓐 Y

/-!
The `n-th` component of this delta functor is denoted `Ext_δ_functor 𝓐 Y n`,
and it is defined on objects as `Ext' n (op X) Y`. -/
example (n : ℕ) (Y : 𝓐) : 𝓐ᵒᵖ ⥤ Ab.{v} := Ext_δ_functor 𝓐 Y n

example (n : ℕ) (X Y : 𝓐) :
  (Ext_δ_functor 𝓐 Y n) (op X) = Ext' n (op X) Y :=
rfl

/-!
`Ext' 0 (X, Y) ≅ Hom(X,Y)`.
-/
example (X Y : 𝓐) : Ext' 0 (op X) Y ≅ AddCommGroup.of (X ⟶ Y) :=
(Ext'_zero_flip_iso _ _).app _

/-!
The isomorphism above is functorial in the first variable, and the isomorphism of functors
is denoted `Ext'_zero_flip_iso 𝓐 Y`. This isomorphism will be used in the example below.
-/
example (Y : 𝓐) : (Ext' 0).flip.obj Y ≅ preadditive_yoneda.obj Y :=
Ext'_zero_flip_iso 𝓐 Y

/-!
Any natural transformation `Hom(-,B) ⟶ F 0` to the zeroth-component of some
delta functor `F` extends in a unique way to a morphism of delta functors
`Ext_δ_functor A B ⟶ F`.

Note that `Ext' 0 (X,B)` is not definitionally equal to `Hom(X,B)`,
so we must compose with the isomorphism `Ext'_zero_flip_iso` from the previous example.
-/
theorem Ext_δ_functor_is_universal_for_Hom
  (Y : 𝓐)
  -- Let `F` be a contravariant delta functor on `𝓐`,
  (F : 𝓐ᵒᵖ ⥤δ Ab.{v})
  -- and `e0` a morphism from `Hom(-,Y)` to `F 0`.
  (e0 : preadditive_yoneda Y ⟶ F 0) :
  -- Then there exists a unique morphism of δ-functors `e : Ext_δ_functor 𝓐 Y ⟶ F`
  ∃! (e : Ext_δ_functor 𝓐 Y ⟶ F),
  -- such that `e0` is the composition of the zero-th component of `e` with the isomorphism
  -- `Hom(-,Y) ≅ Ext' 0 (-,Y)`.
  e0 = (Ext'_zero_flip_iso 𝓐 Y).inv ≫ (e : Ext_δ_functor 𝓐 Y ⟶ F) 0 :=
begin
  let e0' : Ext_δ_functor 𝓐 Y 0 ⟶ F 0 := (Ext'_zero_flip_iso _ _).hom ≫ e0,
  obtain ⟨e,he1,he2⟩ := delta_functor.universal.cond F e0',
  refine ⟨e,_,_⟩,
  { dsimp, simp only [e0', he1, iso.inv_hom_id_assoc], },
  { intros η hη, specialize he2 η,
    apply he2, rw iso.eq_inv_comp at hη,
    exact hη.symm },
end

open AddCommGroup

/-!
An explicit computation: `Ext^1(ℤ/n,ℤ/n) = ℤ/n`.
The notation `AddCommGroup.of A` considers an abelian group `A` as an object of
`AddCommGroup`, the category of abelian groups.
-/
example (n : ℕ) (hn : n ≠ 0) :
  Ext' 1 (op (AddCommGroup.of (zmod n))) (AddCommGroup.of (zmod n)) ≅
  AddCommGroup.of (zmod n) :=
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

end Ext
