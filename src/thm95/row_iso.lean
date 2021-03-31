import thm95.double_complex
import pseudo_normed_group.homotopy

/-!
# A complex canonically isomorphic to `row 1` of the double complex

We have
```
lemma double_complex.row_one :
  (double_complex BD c' r r' V Λ M N).row 1 =
  BD.system c' r V r' (Hom ((cosimplicial Λ N).obj (mk 0)) M) := rfl
```

We want to "rewrite" this row in such a way that it is the target
of the homotopies that will be constructed formally from `BD.homotopy`.

This means that we need to multiply `BD` by `N`,
and then take the system associated with `rescale N (Hom Λ M)`.

We need the following isomorphisms

* `BD.system M^N = (BD.mul N).system M` (Warning: `BD.mul` is not yet defined)
* `Hom (rescale N (Λ^N)) M = (rescale N (Hom Λ M)^N` (2 steps?)
* `(cosimplicial Λ N).obj (mk 0) = rescale N (Λ^N)`

-/

open_locale nnreal

local attribute [instance] type_pow

namespace PolyhedralLattice

section
open simplex_category polyhedral_lattice (conerve.L conerve.obj)

variables (N : ℕ) [fact (0 < N)] (Λ : PolyhedralLattice)
variables (r' : ℝ≥0) (M : ProFiltPseuNormGrpWithTinv r')

-- TODO: we probably want some efficient constructor for these isomorphisms,
-- because the default has a lot of redundancy in the proof obligations

def finsupp_fin_one_iso : of (fin 1 →₀ Λ) ≅ Λ :=
sorry

-- the left hand side is by definition the quotient of the right hand side
-- by a subgroup that is provably trivial
noncomputable def conerve_obj_one_iso :
  of (conerve.obj (diagonal_embedding Λ N) 1) ≅ of (fin 1 →₀ (rescale N (fin N →₀ Λ))) :=
{ hom := sorry,
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

def Hom_rescale_iso [fact (0 < r')] :
  polyhedral_lattice.Hom (rescale N Λ) M ≅
  (ProFiltPseuNormGrpWithTinv.of r' $ (rescale N (polyhedral_lattice.Hom Λ M))) :=
sorry

-- move this
instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (M ^ N) :=
profinitely_filtered_pseudo_normed_group_with_Tinv.pi _ _

def Hom_finsupp_iso [fact (0 < r')] :
  polyhedral_lattice.Hom (fin N →₀ Λ) M ≅
  (ProFiltPseuNormGrpWithTinv.of r' $ ((polyhedral_lattice.Hom Λ M) ^ N)) :=
sorry

end

end PolyhedralLattice
