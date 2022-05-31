import for_mathlib.abelian_sheaves.main
import category_theory.abelian.exact
import category_theory.sites.left_exact
import for_mathlib.chain_complex_exact

universes w v u

open category_theory
open category_theory.limits

variables {C : Type (max v u)} [category.{v} C] {J : grothendieck_topology C}
variables {A : Type w} [category.{max v u} A] [abelian A]
variables [concrete_category.{max v u} A]
variables [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.cover X), limits.has_multiequalizer (S.index P)]
variables [limits.preserves_limits (forget A)]
variables [∀ (X : C), limits.has_colimits_of_shape (J.cover X)ᵒᵖ A]
variables [∀ (X : C), limits.preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget A)]
variables [reflects_isomorphisms (forget A)]

noncomputable theory

-- Just checking...
example : abelian (Sheaf J A) := infer_instance
example : preserves_finite_limits (presheaf_to_Sheaf J A) := infer_instance
example : functor.preserves_zero_morphisms (presheaf_to_Sheaf J A) :=
  infer_instance

-- Missing
instance : preserves_colimits (presheaf_to_Sheaf J A) :=
(sheafification_adjunction J A).left_adjoint_preserves_colimits


.

namespace category_theory.Sheaf

theorem exact_of_exact (X Y Z : Cᵒᵖ ⥤ A) (f : X ⟶ Y) (g : Y ⟶ Z)
  (e : exact f g) :
  exact ((presheaf_to_Sheaf J A).map f) ((presheaf_to_Sheaf J A).map g) :=
begin
  rw abelian.exact_iff at *,
  split,
  { rw [← functor.map_comp, e.1], simp, },
  { let K := kernel g,
    let Q := cokernel f,
    let P := presheaf_to_Sheaf J A,
    let eK : P.obj K ≅ kernel (P.map g) :=
      preserves_kernel.iso _ _,
    let eQ : P.obj Q ≅ cokernel (P.map f) :=
      preserves_cokernel.iso _ _,
    have : kernel.ι (P.map g) =
      eK.inv ≫ P.map (kernel.ι g),
    { dsimp [eK],
      rw iso.eq_inv_comp,
      simp only [preserves_kernel.iso_hom, kernel_comparison_comp_ι] },
    rw this, clear this,
    have : cokernel.π (P.map f) =
      P.map (cokernel.π f) ≫ eQ.hom,
    { dsimp [eQ], rw ← iso.comp_inv_eq,
      simp only [preserves_cokernel.iso_inv, π_comp_cokernel_comparison] },
    rw this, clear this,
    simp only [category.assoc, e.2, ← P.map_comp_assoc,
      P.map_zero, zero_comp, comp_zero] }
end

instance presheaf_to_Sheaf_additive :
  functor.additive (presheaf_to_Sheaf J A) := sorry

lemma map_presheaf_to_Sheaf_homology_zero_of_homology_zero
  (D : chain_complex (Cᵒᵖ ⥤ A) ℕ)
  (h : ∀ i : ℕ, is_zero (D.homology i)) :
  ∀ i : ℕ, is_zero
    ((((presheaf_to_Sheaf J A).map_homological_complex _).obj D).homology i) := sorry
-- Use `exact_of_exact` for this, and the fact that sheafification preserves colimits.

end category_theory.Sheaf

namespace category_theory

instance evaluation_additive (X : C) : functor.additive ((evaluation C A).obj X) := sorry

-- Homology of functors is computed pointwise...
lemma homology_zero_of_eval
  (D : chain_complex (C ⥤ A) ℕ)
  (h : ∀ (X : C) (i : ℕ), is_zero
    (((((evaluation C A).obj X).map_homological_complex _).obj D).homology i)) :
  ∀ i : ℕ, is_zero (D.homology i) := sorry

end category_theory
