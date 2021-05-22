import polyhedral_lattice.cosimplicial
import polyhedral_lattice.Hom
import pseudo_normed_group.system_of_complexes
import system_of_complexes.rescale
import normed_spectral

import simplicial.alternating_face_map

import thm95.modify_complex
import thm95.constants

.

/-!
# The double complex that is the protagonist in the proof of Theorem 9.5
-/

noncomputable theory

open_locale nnreal big_operators
open category_theory opposite simplex_category

universe variables u v w

namespace thm95

variables (BD : breen_deligne.data) (c_ : ℕ → ℝ≥0) [BD.suitable c_]
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : SemiNormedGroup.{v}) [normed_with_aut r V]
variables (Λ : PolyhedralLattice.{u}) (M : ProFiltPseuNormGrpWithTinv.{w} r')
variables (N : ℕ) [fact (0 < N)]

section

open PolyhedralLattice

def Cech_nerve : simplex_category ⥤ (ProFiltPseuNormGrpWithTinv r')ᵒᵖ :=
cosimplicial Λ N ⋙ Hom M

/-- Warning: this is a map in the *opposite* category. -/
def Cech_augmentation_map : (Hom M).obj Λ ⟶ (Cech_nerve r' Λ M N).obj (mk 0) :=
(Hom M).map (cosimplicial_augmentation_map Λ N)

def cosimplicial_system_of_complexes : simplex_category ⥤ system_of_complexes :=
Cech_nerve r' Λ M N ⋙ BD.system c_ r V r'

def augmentation_map :
  (BD.system c_ r V r').obj (op $ polyhedral_lattice.Hom Λ M) ⟶
  (cosimplicial_system_of_complexes BD c_ r r' V Λ M N).obj (mk 0) :=
(BD.system c_ r V r').map (Cech_augmentation_map r' Λ M N)

def double_complex_aux : cochain_complex system_of_complexes ℕ :=
alt_face_map_cocomplex (augmentation_map BD c_ r r' V Λ M N)
begin
  dsimp only [augmentation_map, cosimplicial_system_of_complexes,
    category_theory.functor.comp_map, Cech_augmentation_map, Cech_nerve,
    cosimplicial_augmentation_map, cosimplicial],
  simp only [← (BD.system c_ r V r').map_comp, ← (Hom M).map_comp],
  rw augmentation_map_equalizes (diagonal_embedding Λ N),
end

def double_complex' : system_of_double_complexes :=
(double_complex_aux BD c_ r r' V Λ M N).as_functor

end

section

open polyhedral_lattice
open PolyhedralLattice (of cosimplicial)
open_locale nat

-- we now have a `cochain_complex` of `system_of_complexes`
-- so we need to reorganize the data, to get a `system_of_double_complexes`
-- this is what `.as_functor` does, in the definition `double_complex` below
-- but before we do this, we need to rescale the norms in all the rows,
-- so that the vertical differentials become norm-nonincreasing

def double_complex_aux_rescaled : cochain_complex system_of_complexes ℕ :=
(double_complex_aux BD c_ r r' V Λ M N ).modify
  system_of_complexes.rescale_functor
  system_of_complexes.rescale_nat_trans

def double_complex : system_of_double_complexes :=
(double_complex_aux_rescaled BD c_ r r' V Λ M N).as_functor

lemma double_complex.row_zero :
  (double_complex BD c_ r r' V Λ M N).row 0 =
  (BD.system c_ r V r').obj (op $ Hom Λ M) := rfl

lemma double_complex.row_one :
  (double_complex BD c_ r r' V Λ M N).row 1 =
  (BD.system c_ r V r').obj (op $ Hom ((cosimplicial Λ N).obj (mk 0)) M) := rfl

lemma double_complex.row_map_zero_one :
  (double_complex BD c_ r r' V Λ M N).row_map 0 1 =
  (BD.system c_ r V r').map (Cech_augmentation_map r' Λ M N) :=
begin
  ext c i : 4,
  dsimp only [double_complex, homological_complex.as_functor,
    system_of_double_complexes.row_map_app_f, system_of_double_complexes.d,
    double_complex_aux_rescaled, homological_complex.modify,
    system_of_complexes.rescale_nat_trans, nat_trans.id_app,
    system_of_complexes.rescale_functor, functor.id_map,
    double_complex_aux, alt_face_map_cocomplex],
  erw [category.comp_id, cochain_complex.of_d],
  refl
end

lemma double_complex.row (m : ℕ) :
  (double_complex BD c_ r r' V Λ M N).row (m+2) =
  (system_of_complexes.rescale_functor (m+2)).obj
    ((BD.system c_ r V r').obj (op $ Hom ((cosimplicial Λ N).obj (mk (m+1))) M)) := rfl

end

end thm95

namespace thm95

variables (BD : breen_deligne.data)
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : SemiNormedGroup.{v}) [normed_with_aut r V]
variables (c_ : ℕ → ℝ≥0) [BD.very_suitable r r' c_]
variables (Λ : PolyhedralLattice.{u}) (M : ProFiltPseuNormGrpWithTinv.{w} r')
variables (N : ℕ) [fact (0 < N)]

variables {r r' V c_ Λ M N}

lemma double_complex.row_admissible :
  ∀ m, ((double_complex BD c_ r r' V Λ M N).row m).admissible
| 0     := BD.system_admissible
| 1     := BD.system_admissible
| (m+2) := system_of_complexes.rescale_admissible _ _ BD.system_admissible

lemma double_complex.d_one_norm_noninc (c : ℝ≥0) (q : ℕ) :
  (@system_of_double_complexes.d (double_complex BD c_ r r' V Λ M N) c 1 2 q).norm_noninc :=
begin
  refine ((SemiNormedGroup.to_rescale_bound_by _ _).comp' 2 _ 1 _ _).norm_noninc,
  { norm_num },
  have : (2 : ℝ≥0) = ∑ i : fin 2, 1,
  { simp only [finset.card_fin, mul_one, nat.cast_bit0, finset.sum_const, nsmul_eq_mul, nat.cast_one] },
  dsimp [system_of_complexes.rescale_functor, double_complex_aux, alt_face_map_cocomplex],
  erw [cochain_complex.of_d],
  dsimp [alt_face_map_cocomplex.d, alt_face_map_cocomplex.coboundary],
  simp only [← nat_trans.app_hom_apply, add_monoid_hom.map_sum, add_monoid_hom.map_gsmul,
    ← homological_complex.f_hom_apply, this],
  apply normed_group_hom.bound_by.sum,
  rintro i -,
  refine (normed_group_hom.bound_by.int_smul _ ((-1) ^ ↑i : ℤ)).le (_ : _ * 1 ≤ 1),
  { apply normed_group_hom.norm_noninc.bound_by_one,
    apply breen_deligne.data.complex.map_norm_noninc },
  { simp only [mul_one, int.nat_abs_pow, int.nat_abs_neg, int.nat_abs_one, one_pow, nat.cast_one] },
end
.

lemma double_complex.d_two_norm_noninc (c : ℝ≥0) (p q : ℕ) :
  (@system_of_double_complexes.d (double_complex BD c_ r r' V Λ M N) c (p+2) (p+3) q).norm_noninc :=
begin
  refine ((SemiNormedGroup.scale_bound_by _ _ _).comp' (p+3:ℕ) _ 1 _ _).norm_noninc,
  { simp only [add_zero, nat.add_def, ← nat.cast_succ],
    rw [mul_comm, ← mul_div_assoc, eq_comm, ← nat.cast_mul, nat.factorial_succ], apply div_self,
    norm_cast, norm_num [nat.factorial_ne_zero] },
  apply SemiNormedGroup.rescale_map_bound_by,
  have : (p+1+1+1 : ℝ≥0) = ∑ i : fin (p+1+1+1), 1,
  { simp only [finset.card_fin, mul_one, finset.sum_const, nsmul_eq_mul, nat.cast_id,
      nat.cast_bit1, nat.cast_add, nat.cast_one] },
  dsimp [system_of_complexes.rescale_functor, double_complex_aux, alt_face_map_cocomplex],
  erw [cochain_complex.of_d],
  dsimp [alt_face_map_cocomplex.d, alt_face_map_cocomplex.coboundary],
  simp only [← nat_trans.app_hom_apply, add_monoid_hom.map_sum, add_monoid_hom.map_gsmul,
    ← homological_complex.f_hom_apply, this],
  apply normed_group_hom.bound_by.sum,
  rintro i -,
  refine (normed_group_hom.bound_by.int_smul _ ((-1) ^ ↑i : ℤ)).le (_ : _ * 1 ≤ 1),
  { apply normed_group_hom.norm_noninc.bound_by_one,
    apply breen_deligne.data.complex.map_norm_noninc },
  { simp only [mul_one, int.nat_abs_pow, int.nat_abs_neg, int.nat_abs_one, one_pow, nat.cast_one] },
end

lemma double_complex.d_norm_noninc (c : ℝ≥0) (q : ℕ) :
  ∀ p, (@system_of_double_complexes.d (double_complex BD c_ r r' V Λ M N) c p (p+1) q).norm_noninc
| 0     := breen_deligne.data.complex.map_norm_noninc _ _ _ _ _ _ _ _
| 1     := double_complex.d_one_norm_noninc _ _ _
| (p+2) := double_complex.d_two_norm_noninc _ _ _ _

-- see above: currently we can only prove this for the columns
lemma double_complex_admissible :
  (double_complex BD c_ r r' V Λ M N).admissible :=
system_of_double_complexes.admissible.mk' (double_complex.row_admissible _)
  (by { rintro _ _ _ _ rfl, apply double_complex.d_norm_noninc })

end thm95
