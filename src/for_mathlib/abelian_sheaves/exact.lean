import for_mathlib.abelian_sheaves.main
import category_theory.abelian.exact
import category_theory.abelian.homology
import category_theory.sites.left_exact
import for_mathlib.chain_complex_exact
import for_mathlib.homology_iso
import for_mathlib.exact_functor

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
  functor.additive (presheaf_to_Sheaf J A) :=
begin
  apply_with functor.additive_of_preserves_binary_biproducts { instances := ff },
  apply_with has_binary_biproducts_of_finite_biproducts { instances := ff },
  apply_instance,
  apply preserves_binary_biproducts_of_preserves_binary_coproducts,
  apply_instance,
end

lemma map_presheaf_to_Sheaf_homology_zero_of_homology_zero
  (D : chain_complex (Cᵒᵖ ⥤ A) ℕ)
  (h : ∀ i : ℕ, is_zero (D.homology i)) :
  ∀ i : ℕ, is_zero
    ((((presheaf_to_Sheaf J A).map_homological_complex _).obj D).homology i) :=
begin
  rw ← chain_complex.epi_and_exact_iff_zero_homology' at *,
  split,
  { haveI := h.1, apply_instance },
  { intros i,
    apply exact_of_exact,
    apply h.2 },
end

lemma sheafification_exact : functor.exact (presheaf_to_Sheaf J A) :=
λ X Y Z f g h, exact_of_exact _ _ _ _ _ h

end category_theory.Sheaf

namespace category_theory

instance evaluation_additive (X : C) : functor.additive ((evaluation C A).obj X) :=
⟨λ F G η γ, rfl⟩

def evaluation_homology_iso (X Y Z : C ⥤ A) (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) (t : C) :
  (homology f g w).obj t ≅ (homology (f.app t) (g.app t) $
    by { rw [← nat_trans.comp_app, w], simp, }) :=
{ hom := homology.lift _ _ _
    ((homology.ι f g w).app t ≫ (nat_trans.cokernel_obj_iso f t).hom) begin
      rw category.assoc, let e := _, change _ ≫ e = _,
      have he : e = (cokernel.desc f g w).app t,
      { dsimp [e],
        rw ← iso.eq_inv_comp,
        ext,
        simp },
      rw [he, ← nat_trans.comp_app],
      simp only [homology.condition_ι, nat_trans.app_zero],
    end,
  inv := homology.desc' _ _ _
    ((nat_trans.kernel_obj_iso g t).inv ≫ (homology.π' f g w).app t) begin
      rw ← category.assoc, let e := _, change e ≫ _ = _,
      have he : e = (kernel.lift g f w).app t,
      { dsimp [e], rw iso.comp_inv_eq,
        ext,
        simp },
      rw [he, ← nat_trans.comp_app],
      simp only [homology.condition_π', nat_trans.app_zero],
    end,
  hom_inv_id' := begin
    let a := _, change a ≫ _ = _,
    haveI : epi ((homology.π' f g w).app t),
    { rw abelian.epi_iff_cokernel_π_eq_zero,
      let b := homology.π' f g w,
      have : cokernel.π (b.app t) = (cokernel.π b).app t ≫
        (nat_trans.cokernel_obj_iso b _).hom,
      { simp },
      rw [this, ← iso.eq_comp_inv, zero_comp],
      suffices : cokernel.π b = 0,
      { simp [this], },
      rw ← abelian.epi_iff_cokernel_π_eq_zero,
      dsimp [b, homology.π'],
      apply epi_comp },
    rw ← cancel_epi ((homology.π' f g w).app t),
    have ha : ((homology.π' f g w).app t ≫ a) =
      (nat_trans.kernel_obj_iso _ _).hom ≫ homology.π' _ _ _,
    { dsimp [a],
      apply homology.hom_to_ext,
      simp only [category.assoc, homology.lift_ι, homology.π'_ι,
        nat_trans.kernel_obj_iso_hom_ι_assoc],
      rw [← category.assoc, ← iso.eq_comp_inv],
      simp only [category.assoc, nat_trans.cokernel_obj_iso_π_inv],
      rw [← nat_trans.comp_app, homology.π'_ι, nat_trans.comp_app] },
    rw reassoc_of ha,
    simp only [homology.π'_desc', iso.hom_inv_id_assoc, category.comp_id],
  end,
  inv_hom_id' := begin
    apply homology.hom_from_ext, apply homology.hom_to_ext,
    simp only [category.assoc, homology.π'_desc'_assoc, homology.lift_ι,
      category.comp_id, homology.π'_ι],
    rw [iso.inv_comp_eq, ← category.assoc, ← iso.eq_comp_inv,
      ← nat_trans.comp_app, homology.π'_ι],
    simp,
  end }

-- Homology of functors is computed pointwise...
lemma homology_zero_of_eval
  (D : chain_complex (C ⥤ A) ℕ)
  (h : ∀ (X : C) (i : ℕ), is_zero
    (((((evaluation C A).obj X).map_homological_complex _).obj D).homology i)) :
  ∀ i : ℕ, is_zero (D.homology i) :=
begin
  rw ← chain_complex.epi_and_exact_iff_zero_homology',
  split,
  { apply_with nat_trans.epi_app_of_epi { instances := ff },
    intros X,
    specialize h X,
    rw ← chain_complex.epi_and_exact_iff_zero_homology' at h,
    exact h.1 },
  { intros i, rw preadditive.exact_iff_homology_zero,
    refine ⟨_,_⟩,
    { ext X, specialize h X,
      rw ← chain_complex.epi_and_exact_iff_zero_homology' at h, replace h := h.2 i,
      rw preadditive.exact_iff_homology_zero at h,
      obtain ⟨w,hw⟩ := h, exact w },
    { refine ⟨is_zero.iso_zero _⟩,
      apply functor.is_zero,
      intros X,
      specialize h X (i+1),
      refine is_zero.of_iso _ (evaluation_homology_iso _ _ _ _ _ _ _),
      apply is_zero.of_iso h,
      symmetry, apply homology_iso; exact rfl } }
end

end category_theory
