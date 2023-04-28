import Lbar.pseudo_normed_group
import pseudo_normed_group.strongly_splittable

universe u

noncomputable theory
open_locale big_operators nnreal
open pseudo_normed_group

variables {r' : ℝ≥0} {S : Type u} [fact (0 < r')] [fintype S]

namespace Lbar

instance strongly_splittable (N : ℕ) [fact (0 < N)] : strongly_splittable (Lbar r' S) N 1 :=
sorry

end Lbar
