import algebra.homology.homotopy
import category_theory.limits.shapes.zero_objects

import for_mathlib.Cech.split
import for_mathlib.abelian_category

noncomputable theory

universes v u v' u'

namespace category_theory
open_locale simplicial
open category_theory.limits

namespace arrow

section contravariant
variables {P : Type u} {N : Type u'} [category.{v} P] [category.{v'} N] (M : Pᵒᵖ ⥤ N)
variables (f : arrow P)
variables [∀ n : ℕ, has_wide_pullback f.right (λ i : (fin (n+1)), f.left) (λ i, f.hom)]
variables [arrow.split f] [preadditive N]

def contracting_homotopy' : homotopy (𝟙 (f.conerve M).to_cocomplex) 0 :=
{ hom := λ i j, if h : j + 1 = i then eq_to_hom (by subst h) ≫ f.contracting_homotopy M j else 0,
  zero' := λ i j h, dif_neg h,
  comm := λ i, begin
    simp only [homological_complex.id_f, homotopy.d_next_cochain_complex,
      homological_complex.zero_f_apply, add_zero],
    rcases i with _|_|i,
    { rw [← is_contracting_homotopy_zero, homotopy.prev_d_zero_cochain_complex],
      simp only [eq_self_iff_true, dif_pos, eq_to_hom_refl, category.id_comp, add_zero], },
    { rw [← is_contracting_homotopy_one, homotopy.prev_d_succ_cochain_complex],
      simp only [eq_self_iff_true, dif_pos, eq_to_hom_refl, category.id_comp, add_zero], },
    { rw [← is_contracting_homotopy, homotopy.prev_d_succ_cochain_complex],
      simp only [eq_self_iff_true, dif_pos, eq_to_hom_refl, category.id_comp, add_zero], },
  end }

variables [has_equalizers N] [has_cokernels N] [has_images N] [has_image_maps N]

lemma conerve_to_cocomplex_homology_is_zero (i : ℕ) :
  is_zero ((f.conerve M).to_cocomplex.homology i) :=
begin
  rw is_zero_iff_id_eq_zero,
  simpa only [category_theory.functor.map_id, functor.map_zero] using
    homology_map_eq_of_homotopy (f.contracting_homotopy' M) i,
end

end contravariant

section covariant

variables {P : Type u} {N : Type u'} [category.{v} P] [category.{v'} N] (M : P ⥤ N)
variables (f : arrow P)
variables [∀ n : ℕ, has_wide_pullback f.right (λ i : (fin (n+1)), f.left) (λ i, f.hom)]
variables [arrow.split f] [preadditive N]

def covariant_contracting_homotopy' : homotopy (𝟙 (f.nerve M).to_complex) 0 :=
{ hom := λ i j, if h : i + 1 = j then
    f.covariant_contracting_homotopy M i ≫ eq_to_hom (by subst h) else 0,
  zero' := λ i j h, dif_neg h,
  comm := λ i, begin
    simp only [homological_complex.id_f, homotopy.d_next_cochain_complex,
      homological_complex.zero_f_apply, add_zero],
    rcases i with _|_|i,
    { rw [← covariant_is_contracting_homotopy_zero, homotopy.d_next_zero_chain_complex],
      simp only [eq_self_iff_true, eq_to_hom_refl, dite_eq_ite, if_true,
        homotopy.prev_d_chain_complex, category.comp_id, zero_add] },
    { rw [← covariant_is_contracting_homotopy_one, homotopy.d_next_succ_chain_complex],
      simp only [simplicial_object.augmented.to_complex_d_2, eq_self_iff_true,
        eq_to_hom_refl, category.id_comp, dite_eq_ite, if_true,
        category.comp_id, homotopy.prev_d_chain_complex],
      rw add_comm },
    { rw [← covariant_is_contracting_homotopy, homotopy.d_next_succ_chain_complex],
      simp only [simplicial_object.augmented.to_complex_d_2, eq_self_iff_true,
        eq_to_hom_refl, category.id_comp, dite_eq_ite, if_true,
        category.comp_id, homotopy.prev_d_chain_complex],
      rw add_comm },
  end }

variables [has_equalizers N] [has_cokernels N] [has_images N] [has_image_maps N]

lemma nerve_to_complex_homology_is_zero (i : ℕ) :
  is_zero ((f.nerve M).to_complex.homology i) :=
begin
  rw is_zero_iff_id_eq_zero,
  simpa only [category_theory.functor.map_id, functor.map_zero] using
    homology_map_eq_of_homotopy (f.covariant_contracting_homotopy' M) i,
end

end covariant

end arrow

end category_theory
