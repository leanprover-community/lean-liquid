import algebra.homology.functor

import for_mathlib.simplicial.complex

import polyhedral_lattice.cosimplicial
import polyhedral_lattice.Hom
import pseudo_normed_group.system_of_complexes
import system_of_complexes.rescale
import normed_spectral

import thm95.modify_complex
import thm95.polyhedral_iso

/-!
# The double complex that is the protagonist in the proof of Theorem 9.5
-/

noncomputable theory

open_locale nnreal big_operators
open category_theory opposite simplex_category

universe variables u v

namespace thm95

variables (BD : breen_deligne.data) (κ : ℕ → ℝ≥0) [BD.suitable κ]
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : SemiNormedGroup.{v}) [normed_with_aut r V]
variables (Λ : PolyhedralLattice.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r')
variables (N : ℕ) [fact (0 < N)]

section

open PolyhedralLattice

def Cech_nerve : cosimplicial_object.augmented (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ :=
(cosimplicial_object.augmented.whiskering_obj _ _ (Hom.{u u} M).right_op).obj
  (augmented_cosimplicial.{u} Λ N)

def Cech_augmentation_map : ((Cech_nerve r' Λ M N).right.obj (mk 0)).unop ⟶ (Hom M).obj (op Λ) :=
(Hom M).map (cosimplicial_augmentation_map Λ N).op

lemma Cech_nerve_hom_zero :
  (Cech_nerve.{u} r' Λ M N).hom.app (mk 0) = (Cech_augmentation_map.{u} r' Λ M N).op :=
begin
  dsimp only [Cech_nerve, Cech_augmentation_map, cosimplicial_object.augmented.whiskering_obj],
  simp only [whisker_right_app, category.id_comp, functor.right_op_map, nat_trans.comp_app,
    functor.const_comp_inv_app],
  congr' 2,
  dsimp only [augmented_cosimplicial, augmented_Cech_conerve],
  rw cosimplicial_object.augment_hom_zero,
  refl
end

lemma _root_.PolyhedralLattice.Cech_augmentation_map_eq_Hom_sum :
  (Λ.Hom_cosimplicial_zero_iso N r' M ↑N rfl).inv ≫ (thm95.Cech_augmentation_map r' Λ M N) =
  (Hom_sum Λ N r' M) :=
begin
  dsimp only [thm95.Cech_augmentation_map, Hom_cosimplicial_zero_iso,
    Hom_cosimplicial_zero_iso_aux_rfl, Hom_cosimplicial_zero_iso'],
  rw [iso.refl_trans, iso.refl_trans],
  dsimp only [iso.trans_inv, functor.map_iso_hom, functor.map_iso_inv, iso.symm_inv, op_comp],
  simp only [category.assoc, ← (Hom M).map_comp, augmentation_eq_diagonal, iso.op_hom, ← op_comp],
  dsimp only [Hom_rescale_iso, Hom_finsupp_iso],
  ext f l : 2,
  exact finsupp_sum_diagonal_embedding Λ N r' M f l,
end

def cosimplicial_system_of_complexes : cosimplicial_object.augmented system_of_complexes :=
(cosimplicial_object.augmented.whiskering_obj.{u} _ _ (BD.system κ r V r')).obj
  (Cech_nerve r' Λ M N)

lemma cosimplicial_system_of_complexes_hom_zero :
  (cosimplicial_system_of_complexes BD κ r r' V Λ M N).hom.app (mk 0) =
  (BD.system κ r V r').map (Cech_augmentation_map.{u} r' Λ M N).op :=
begin
  ext : 2, dsimp [cosimplicial_system_of_complexes],
  rw [category.id_comp, Cech_nerve_hom_zero]
end

@[simps X d]
def double_complex_aux : cochain_complex system_of_complexes ℕ :=
(cosimplicial_system_of_complexes BD κ r r' V Λ M N).to_cocomplex
.

@[simps obj map]
def double_complex' : system_of_double_complexes :=
(double_complex_aux BD κ r r' V Λ M N).as_functor

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

set_option pp.universes true

@[simps X d]
def double_complex_aux_rescaled : cochain_complex system_of_complexes ℕ :=
@homological_complex.modify _ _ _ _ _ _ _ _
(double_complex_aux BD κ r r' V Λ M N )
  system_of_complexes.rescale_functor
  system_of_complexes.rescale_nat_trans
  (system_of_complexes.rescale_functor.additive)

@[simps obj map]
def double_complex : system_of_double_complexes :=
(double_complex_aux_rescaled BD κ r r' V Λ M N).as_functor

lemma double_complex.row_zero :
  (double_complex BD κ r r' V Λ M N).row 0 =
  (BD.system κ r V r').obj (op $ Hom Λ M) := rfl

lemma double_complex.row_one :
  (double_complex BD κ r r' V Λ M N).row 1 =
  (BD.system κ r V r').obj (op $ Hom ((cosimplicial Λ N).obj (mk 0)) M) := rfl

lemma double_complex.row_map_zero_one :
  (double_complex BD κ r r' V Λ M N).row_map 0 1 =
  (BD.system κ r V r').map (Cech_augmentation_map r' Λ M N).op :=
begin
  ext c i : 4,
  dsimp only [system_of_double_complexes.row_map_app_f, system_of_double_complexes.d,
    double_complex, homological_complex.as_functor_obj,
    double_complex_aux_rescaled, homological_complex.modify,
    system_of_complexes.rescale_nat_trans, nat_trans.id_app,
    system_of_complexes.rescale_functor, functor.id_map, double_complex_aux, op_unop],
  erw [category.comp_id, ← Cech_nerve_hom_zero],
  simp only [dite_eq_ite, breen_deligne.data.system_map, if_true, eq_self_iff_true,
    cosimplicial_object.augmented.to_cocomplex_d_2, eq_to_hom_refl, category.comp_id],
  dsimp only [cosimplicial_object.augmented.to_cocomplex_d,
    cosimplicial_system_of_complexes, cosimplicial_object.augmented.whiskering_obj],
  simp only [breen_deligne.data.system_map, whisker_right_app, category.id_comp,
    nat_trans.comp_app, functor.const_comp_inv_app],
  refl
end

lemma double_complex.row (m : ℕ) :
  (double_complex BD κ r r' V Λ M N).row (m+2) =
  (system_of_complexes.rescale_functor (m+2)).obj
    ((BD.system κ r V r').obj (op $ Hom ((cosimplicial Λ N).obj (mk (m+1))) M)) := rfl

end

end thm95

namespace thm95

variables (BD : breen_deligne.data)
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : SemiNormedGroup.{v}) [normed_with_aut r V]
variables (κ : ℕ → ℝ≥0) [BD.very_suitable r r' κ]
variables (Λ : PolyhedralLattice.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r')
variables (N : ℕ) [fact (0 < N)]

variables {r r' V κ Λ M N}

lemma double_complex.row_admissible :
  ∀ m, ((double_complex BD κ r r' V Λ M N).row m).admissible
| 0     := BD.system_admissible
| 1     := BD.system_admissible
| (m+2) := system_of_complexes.rescale_admissible _ _ BD.system_admissible

lemma double_complex.d_one_norm_noninc (c : ℝ≥0) (q : ℕ) :
  (@system_of_double_complexes.d (double_complex BD κ r r' V Λ M N) c 1 2 q).norm_noninc :=
begin
  apply normed_add_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.2,
  refine normed_add_group_hom.norm_comp_le_of_le' 2 _ 1 _ (SemiNormedGroup.norm_to_rescale_le _ _) _,
  { norm_num },
  have : (2 : ℝ) = ∑ i : fin 2, 1,
  { simp only [finset.card_fin, mul_one, nat.cast_bit0, finset.sum_const, nsmul_eq_mul, nat.cast_one] },
  dsimp [system_of_complexes.rescale_functor, double_complex_aux,
    cosimplicial_object.augmented.to_cocomplex_d],
  erw [category.comp_id, if_pos rfl],
  dsimp [cosimplicial_object.coboundary],
  simp only [← nat_trans.app_hom_apply, add_monoid_hom.map_sum, add_monoid_hom.map_zsmul,
    ← homological_complex.hom.f_add_monoid_hom_apply, this],
  apply norm_sum_le_of_le,
  rintro i -,
  refine le_trans (norm_zsmul_le _ _) _,
  rw [← int.norm_cast_real, int.cast_pow, norm_pow, int.cast_neg, int.cast_one, norm_neg, norm_one,
    one_pow, one_mul],
  apply normed_add_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.1,
  apply breen_deligne.data.complex.map_norm_noninc
end
.

lemma double_complex.d_two_norm_noninc (c : ℝ≥0) (p q : ℕ) :
  (@system_of_double_complexes.d (double_complex BD κ r r' V Λ M N) c (p+2) (p+3) q).norm_noninc :=
begin
  apply normed_add_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.2,
  refine normed_add_group_hom.norm_comp_le_of_le' (p+3:ℕ) _ 1 _ (SemiNormedGroup.norm_scale_le _ _ _) _,
  { simp only [add_zero, nat.add_def, ← nat.cast_succ],
    norm_cast,
    rw [mul_comm, ← mul_div_assoc, eq_comm, ← nat.cast_mul, nat.factorial_succ], apply div_self,
    norm_num [nat.factorial_ne_zero] },
  apply SemiNormedGroup.norm_rescale_map_le,
  have : ((p+3:ℕ) : ℝ) = ∑ i : fin (p+3), 1,
  { simp only [finset.card_fin, mul_one, finset.sum_const, nsmul_eq_mul, nat.cast_id,
      nat.cast_bit1, nat.cast_add, nat.cast_one] },
  dsimp [system_of_complexes.rescale_functor, double_complex_aux,
    cosimplicial_object.augmented.to_cocomplex_d],
  erw [category.comp_id, if_pos rfl],
  dsimp [cosimplicial_object.coboundary],
  simp only [← nat_trans.app_hom_apply, add_monoid_hom.map_sum, add_monoid_hom.map_zsmul,
    ← homological_complex.hom.f_add_monoid_hom_apply, this],
  apply norm_sum_le_of_le,
  rintro i -,
  refine le_trans (norm_zsmul_le _ _) _,
  rw [← int.norm_cast_real, int.cast_pow, norm_pow, int.cast_neg, int.cast_one, norm_neg, norm_one,
    one_pow, one_mul],
  apply normed_add_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.1,
  apply breen_deligne.data.complex.map_norm_noninc
end

lemma double_complex.d_norm_noninc (c : ℝ≥0) (q : ℕ) :
  ∀ p, (@system_of_double_complexes.d (double_complex BD κ r r' V Λ M N) c p (p+1) q).norm_noninc
| 0     := breen_deligne.data.complex.map_norm_noninc _ _ _ _ _ _ _ _
| 1     := double_complex.d_one_norm_noninc _ _ _
| (p+2) := double_complex.d_two_norm_noninc _ _ _ _

-- see above: currently we can only prove this for the columns
lemma double_complex_admissible :
  (double_complex BD κ r r' V Λ M N).admissible :=
system_of_double_complexes.admissible.mk' (double_complex.row_admissible _)
  (by { rintro _ _ _ _ rfl, apply double_complex.d_norm_noninc })

end thm95
