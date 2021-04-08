import rescale.pseudo_normed_group
import pseudo_normed_group.FiltrationPow

open_locale classical nnreal
open ProFiltPseuNormGrpWithTinv

universe variables u

@[simp] theorem Filtration_rescale (r' c N : ℝ≥0) [fact (0 < r')]
  (M) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  ((Filtration r').obj c).obj (of r' (rescale N M)) =
  ((Filtration r').obj (c * N⁻¹)).obj (of r' M) := rfl
