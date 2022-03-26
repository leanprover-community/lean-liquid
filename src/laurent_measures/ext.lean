
import for_mathlib.derived.les_facts
import laurent_measures.ses2
import challenge_notations

.

universe u

open category_theory
open_locale nnreal

namespace laurent_measures

variables (r r' : ℝ≥0) [fact (0 < r)] [fact (r < r')] [fact (r' < 1)] (S : Profinite.{u})
variables

-- move me
instance fact_half_pos : fact ((0:ℝ≥0) < 1/2) := sorry

-- move me
instance fact_pos_of_half_lt : fact (0 < r') := sorry

lemma epi_and_is_iso (V : SemiNormedGroup.{u}) [normed_with_aut r V] [complete_space V]
  (hV : ∀ (v : V), (normed_with_aut.T.inv v) = 2 • v) :
  epi (((Ext' 0).map ((condensify_Tinv2 (fintype_functor r')).app S).op).app
    (Condensed.of_top_ab V)) ∧
  ∀ i > 0, is_iso (((Ext' i).map ((condensify_Tinv2 (fintype_functor r')).app S).op).app
    (Condensed.of_top_ab V)) :=
begin
  sorry
end


end laurent_measures
