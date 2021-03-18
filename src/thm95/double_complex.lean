import polyhedral_lattice.cosimplicial
import polyhedral_lattice.Hom
import pseudo_normed_group.system_of_complexes

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

def Cech_nerve : simplicial_object (ProFiltPseuNormGrpWithTinv r') :=
(PolyhedralLattice.cosimplicial Λ N).op ⋙ PolyhedralLattice.Hom M

def Cech_augmentation_map : (Cech_nerve r' Λ M N).obj (op $ mk 0) ⟶ Hom Λ M :=
(PolyhedralLattice.Hom M).map
  (PolyhedralLattice.cosimplicial_augmentation_map Λ N).op

-- def double_complex := sorry

end thm95
