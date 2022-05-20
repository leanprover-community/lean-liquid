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

variables {P : Type u} {N : Type u'} [category.{v} P] [category.{v'} N] (M : Pᵒᵖ ⥤ N)
variables (f : arrow P)
variables [∀ n : ℕ, has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]
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

variables [has_equalizers N] [has_cokernels N] [has_images N] [has_image_maps N] [has_zero_object N]

lemma conerve_to_cocomplex_homology_is_zero (i : ℕ) :
  is_zero ((f.conerve M).to_cocomplex.homology i) :=
begin
  rw is_zero_iff_id_eq_zero,
  simpa only [category_theory.functor.map_id, functor.map_zero] using
    homology_map_eq_of_homotopy (f.contracting_homotopy' M) i,
end

end arrow

end category_theory
