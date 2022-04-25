
import for_mathlib.derived.les_facts
import laurent_measures.ses2
import invpoly.ses
import Lbar.ses
import Lbar.ext
import free_pfpng.acyclic
import challenge_notations

.

universe u

open category_theory
open_locale nnreal

namespace laurent_measures

variables (r r' : ℝ≥0) [fact (0 < r)] [fact (r < r')] [fact (r' < 1)] (S : Profinite.{u})
variables

-- move me
instance fact_half_pos : fact ((0:ℝ≥0) < 1/2) := ⟨by simp⟩

lemma epi_and_is_iso [fact (0 < r')]
  (V : SemiNormedGroup.{u}) [normed_with_aut r V] [complete_space V] [separated_space V]
  (hV : ∀ (v : V), (normed_with_aut.T.inv v) = 2 • v) :
  epi (((Ext' 0).map ((condensify_Tinv2 (fintype_functor r')).app S).op).app
    (Condensed.of_top_ab V)) ∧
  ∀ i > 0, is_iso (((Ext' i).map ((condensify_Tinv2 (fintype_functor r')).app S).op).app
    (Condensed.of_top_ab V)) :=
begin
  have SES := Lbar.short_exact.{u u} r' S,
  haveI : fact (r < 1) := ⟨(fact.out _ : r < r').trans (fact.out _)⟩,
  rw ← epi_and_is_iso_iff_of_is_iso _ _ _ _
    ((condensify_Tinv2 _).app S) ((condensify_Tinv2 _).app S) ((condensify_Tinv2 _).app S)
    _ _ (Condensed.of_top_ab V) SES SES (Lbar.is_iso_Tinv2 r r' S V hV),
  { rw ← is_zero_iff_epi_and_is_iso _ _ _ (invpoly.short_exact r' S),
    apply free_pfpng_acyclic, },
  { rw [← nat_trans.comp_app, condensify_map_comp_Tinv2, nat_trans.comp_app], },
  { rw [← nat_trans.comp_app, condensify_map_comp_Tinv2, nat_trans.comp_app], }
end


end laurent_measures
