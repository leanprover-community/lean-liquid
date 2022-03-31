import free_pfpng.main
import invpoly.functor
import condensed.condensify

universe u

noncomputable theory

open category_theory

open_locale nnreal

namespace invpoly
open ProFiltPseuNormGrpWithTinv₁

variables (r : ℝ≥0) [fact (0 < r)] [fact (r < 1)]

@[simps] def eval2 (S : Fintype.{u}) :
  strict_comphaus_filtered_pseudo_normed_group_hom (invpoly r S) (free_pfpng S) :=
{ to_fun := λ F s, (F s).eval 2,
  map_zero' := by { ext, simp only [polynomial.eval_zero, pi.zero_apply], },
  map_add' := by { intros, ext, simp only [polynomial.eval_add, pi.add_apply], },
  strict' := λ c F hF, sorry,
  continuous' := λ c, begin
    sorry
  end }

lemma eval2_surjective (S : Fintype.{u}) :
  function.surjective (eval2 r S) :=
begin
  intro y,
  let F : invpoly r S := λ s, polynomial.C (y s),
  use F,
  ext s,
  simp only [eval2_to_fun, polynomial.eval_C],
end

def eval2_nat_trans :
  (fintype_functor.{u} r ⋙ to_CompHausFiltPseuNormGrp₁.{u} r) ⟶
  (free_pfpng_functor.{u} ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) :=
{ app := λ S, eval2 r S,
  naturality' := λ S T f, by { ext x t, sorry } }
.

section ses

open CompHausFiltPseuNormGrp₁

theorem short_exact (S : Profinite) :
  short_exact ((condensify_Tinv2 _).app S) ((condensify_map $ eval2_nat_trans r).app S) :=
begin
  refine condensify_nonstrict_exact _ _ (r⁻¹ + 2) (Tinv2_bound_by _) sorry _ sorry _ _ _ _ _ _ _,
  swap 6, { apply eval2_surjective },
  all_goals { sorry },
end

end ses

end invpoly