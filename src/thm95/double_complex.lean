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

open_locale nnreal
open category_theory opposite simplex_category

namespace thm95

universe variables u v w

variables (BD : breen_deligne.data) (c' : ℕ → ℝ≥0) [BD.suitable c']
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : NormedGroup.{v}) [normed_with_aut r V]
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
Cech_nerve r' Λ M N ⋙ BD.System c' r V r'

def augmentation_map :
  (BD.System c' r V r').obj (op $ polyhedral_lattice.Hom Λ M) ⟶
  (cosimplicial_system_of_complexes BD c' r r' V Λ M N).obj (mk 0) :=
(BD.System c' r V r').map (Cech_augmentation_map r' Λ M N)

def double_complex_aux : cochain_complex ℕ system_of_complexes :=
alt_face_map_cocomplex (augmentation_map BD c' r r' V Λ M N)
begin
  sorry
  /-
  show (BD.System c' r V r').map (Cech_augmentation_map r' Λ M N) ≫
        (BD.System c' r V r').map ((Cech_nerve r' Λ M N).map (δ 0)) =
       (BD.System c' r V r').map (Cech_augmentation_map r' Λ M N) ≫
        (BD.System c' r V r').map ((Cech_nerve r' Λ M N).map (δ 1)),
  simp only [← (BD.System c' r V r').map_comp],
  congr' 1,
  show (Hom M).map (cosimplicial_augmentation_map Λ N) ≫
        (Hom M).map ((Λ.cosimplicial N).map (δ 0)) =
       (Hom M).map (cosimplicial_augmentation_map Λ N) ≫
        (Hom M).map ((Λ.cosimplicial N).map (δ 1)),
  simp only [← (Hom M).map_comp],
  congr' 1,
  apply augmentation_map_equalizes
  -/
end

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

def double_complex_aux_rescaled : cochain_complex ℕ system_of_complexes :=
(double_complex_aux BD c' r r' V Λ M N ).modify
  system_of_complexes.rescale_functor
  system_of_complexes.rescale_nat_trans

def double_complex : system_of_double_complexes :=
(double_complex_aux_rescaled BD c' r r' V Λ M N).as_functor ℕ _

lemma double_complex.row_zero :
  (double_complex BD c' r r' V Λ M N).row 0 = BD.system c' r V r' (Hom Λ M) := rfl

lemma double_complex.row_one :
  (double_complex BD c' r r' V Λ M N).row 1 =
  BD.system c' r V r' (Hom ((cosimplicial Λ N).obj (mk 0)) M) := rfl

lemma double_complex.row (m : ℕ) :
  (double_complex BD c' r r' V Λ M N).row (m+2) =
  (system_of_complexes.rescale_functor (m+2)).obj
    (BD.system c' r V r' (Hom ((cosimplicial Λ N).obj (mk (m+1))) M)) := rfl

variables {BD c' r r' V Λ M}

-- the following two lemmas are currently not provable,
-- we need a stronger assumption than `[BD.suitable c']`
-- this is WIP
lemma system_admissible : (BD.system c' r V r' (Hom Λ M)).admissible :=
sorry

-- see above: currently we can only prove this for the columns
lemma double_complex_admissible :
  (double_complex BD c' r r' V Λ M N).admissible :=
{ d_norm_noninc' := sorry,  /- ← should be provable -/
  d'_norm_noninc' := sorry, /- ← this should be provable assuming `system_admissible` above;
                                 also note `system_of_complexes.rescale_admissible` -/
  res_norm_noninc := sorry, /- ← should be provable -/ }

end

end thm95
