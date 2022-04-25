import for_mathlib.derived.les2
.

noncomputable theory

open category_theory category_theory.limits opposite
open homotopy_category (hiding single)
open bounded_homotopy_category

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]

variables (C : cochain_complex 𝓐 ℤ)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj C)]

def compute_with_acyclic
  (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B))
  (i : ℤ) :
  ((Ext i).obj (op $ of' C)).obj ((single _ 0).obj B) ≅
  unop ((((preadditive_yoneda.obj B).right_op.map_homological_complex _).obj C).homology i) :=
begin
  let P := (of' C).replace,
  let π : P ⟶ of' C := (of' C).π,
  let B' := (single _ 0).obj B,
  let HomB := (preadditive_yoneda.obj B).right_op.map_homotopy_category (complex_shape.up ℤ),
  let f := HomB.map π,
  suffices hf : is_quasi_iso f,
  { resetI,
    let e := as_iso ((homotopy_category.homology_functor Abᵒᵖ _ i).map f),
    let e' := e.symm.unop,
    refine _ ≪≫ e',
    -- currently there are some `op`s in the wrong places
    -- so this is provable, but requires identifying the `op` of homology with the homology of `op`s
    sorry },
  have := cone_triangleₕ_mem_distinguished_triangles _ _ f.out,
  replace := is_quasi_iso_iff_is_acyclic _ this,
  dsimp [homological_complex.cone.triangleₕ] at this,
  simp only [quotient_map_out] at this,
  rw this, clear this,
  constructor,
  intro i,
  refine is_zero.of_iso _ (homology_iso _ (i-1) i (i+1) _ _),
  rotate, { exact add_sub_cancel _ _ }, { dsimp, refl },
  apply exact.homology_is_zero _,
  rw ← abelian.exact.unop_iff,
  sorry
end
