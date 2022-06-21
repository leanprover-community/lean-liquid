import algebra.category.Group.colimits
import algebra.module.basic
import category_theory.limits.has_limits
import group_theory.torsion

/--
The main result is the final `theorem flat_of_tf` stating that a torsion-free abelian group (

-/

noncomputable theory

open category_theory monoid category_theory.limits function linear_map

section tf_colimit

variables {G : Type} [add_comm_group G]

def index_category_of_tf (hG : no_zero_smul_divisors ℤ G) : Cat := sorry

def index_functor_of_tf (hG : no_zero_smul_divisors ℤ G) :
  (index_category_of_tf hG) ⥤ AddCommGroup := sorry

instance index_concrete [hG : no_zero_smul_divisors ℤ G] : concrete_category
 (index_category_of_tf hG) := sorry

instance has_colimit_of_tf [hG : no_zero_smul_divisors ℤ G] :
 has_colimit (index_functor_of_tf hG) := sorry

lemma colimit_of_torsion_free (hG : no_zero_smul_divisors ℤ G) : G ≃+
 (colimit (index_functor_of_tf hG)).1 := sorry

end tf_colimit

section aux_flatness

lemma flat_of_fg_free {G M N : Type} [add_comm_group G] [add_comm_group M] [add_comm_group N]
  (hG : no_zero_smul_divisors ℤ G) {k : ℕ} (b : basis (fin k) ℤ G) {φ : M →ₗ[ℤ] N}
  (hφ : injective φ) : injective (rtensor G φ) := sorry

lemma colimit_left_exact {J : Type*} [category J] [concrete_category J] {M : J ⥤ AddCommGroup}
 {N : J ⥤ AddCommGroup} (hM : has_colimit M) (hN : has_colimit N) {φ : M ⟶ N}
 (hφ : ∀ j : J, injective (φ.app j)) : injective (colim_map φ) := sorry

end aux_flatness

theorem flat_of_tf {G M N : Type} [add_comm_group G] [add_comm_group M] [add_comm_group N]
  (hG : no_zero_smul_divisors ℤ G) {φ : M →ₗ[ℤ] N} (hφ : injective φ) : injective (rtensor G φ) :=
begin
  sorry,
end
