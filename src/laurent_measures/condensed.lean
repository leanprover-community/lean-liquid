import laurent_measures.functor
import condensed.ab

noncomputable theory

universe u

open category_theory

open_locale nnreal

-- move me
def ProFiltPseuNormGrpWithTinv₁.to_CompHausFiltPseuNormGrp₁ (r' : ℝ≥0) [fact (0 < r')] :
  ProFiltPseuNormGrpWithTinv₁ r' ⥤ CompHausFiltPseuNormGrp₁ :=
{ obj := λ M,
  { M := M,
    str := infer_instance,
    exhaustive' := M.exhaustive _ },
  map := λ M N f, {..f},
  map_id' := λ M, by { ext, refl },
  map_comp' := by { intros, ext, refl } }

namespace laurent_measures

def condensed (r' : ℝ≥0) [fact (0 < r')] : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
  laurent_measures.functor.{u u} r' ⋙
    ProFiltPseuNormGrpWithTinv₁.to_CompHausFiltPseuNormGrp₁.{u u} r' ⋙
    CompHausFiltPseuNormGrp₁.to_Condensed

end laurent_measures
