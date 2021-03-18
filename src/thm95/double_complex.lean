import polyhedral_lattice.cosimplicial
import polyhedral_lattice.Hom
import pseudo_normed_group.system_of_complexes

import simplicial.alternating_face_map

import thm95.constants

.

/-!
# The double complex that is the protagonist in the proof of Theorem 9.5
-/

noncomputable theory

open_locale nnreal
open category_theory opposite simplex_category polyhedral_lattice

namespace thm95

variables (BD : breen_deligne.package) (c' : ℕ → ℝ≥0) [BD.suitable c']
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : NormedGroup) [normed_with_aut r V]
variables (Λ : PolyhedralLattice) (M : ProFiltPseuNormGrpWithTinv r')
variables (N : ℕ) [fact (0 < N)]

def Cech_nerve : simplex_category ⥤ (ProFiltPseuNormGrpWithTinv r')ᵒᵖ :=
PolyhedralLattice.cosimplicial Λ N ⋙ PolyhedralLattice.Hom M

/-- Warning: this is a map in the *opposite* category. -/
def Cech_augmentation_map :
  (PolyhedralLattice.Hom M).obj Λ ⟶ (Cech_nerve r' Λ M N).obj (mk 0) :=
(PolyhedralLattice.Hom M).map (PolyhedralLattice.cosimplicial_augmentation_map Λ N)

def cosimplicial_system_of_complexes : simplex_category ⥤ system_of_complexes :=
Cech_nerve r' Λ M N ⋙ BD.System c' r V r'

def augmentation_map :
  (BD.System c' r V r').obj (op $ Hom Λ M) ⟶
  (cosimplicial_system_of_complexes BD c' r r' V Λ M N).obj (mk 0) :=
(BD.System c' r V r').map (Cech_augmentation_map r' Λ M N)

def double_complex : @cochain_complex ℕ system_of_complexes _ _ _ :=
alt_face_map_cocomplex (augmentation_map BD c' r r' V Λ M N) sorry

end thm95
