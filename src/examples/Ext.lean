import challenge_notations
import challenge_prerequisites

/-!

This file shows that `Ext` is a universal δ-functor (TODO)
and performs the computation `Ext^1(ℤ/nℤ, ℤ/nℤ) = ℤ/nℤ`.

-/

noncomputable theory

open category_theory category_theory.limits opposite

namespace AddCommGroup

example (n : ℕ) (hn : n ≠ 0) :
  ((Ext' 1).obj (op $ of $ zmod n)).obj (of $ zmod n) ≅ of (zmod n) :=
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
