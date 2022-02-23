import laurent_measures.ses
import laurent_measures.condensed
import real_measures.condensed
import condensed.exact

universe u

noncomputable theory

open category_theory

open_locale nnreal

namespace laurent_measures

variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]

local notation `r` := @r p


open laurent_measures_ses

def Θ (S : Fintype.{u}) :
  (fintype_functor.{u} r ⋙
    ProFiltPseuNormGrpWithTinv₁.to_CompHausFiltPseuNormGrp₁.{u u} r).obj S ⟶
  (real_measures.functor p).obj S :=
strict_comphaus_filtered_pseudo_normed_group_hom.mk' (θ_to_add p)
begin
  intro c,
  use θ_bound' p c,
  convert continuous_θ_c p S c,
  simp only [θ_c, one_mul, eq_mpr_eq_cast, set_coe_cast],
  refl,
end

def Θ_fintype_nat_trans :
  (fintype_functor.{u} r ⋙
    ProFiltPseuNormGrpWithTinv₁.to_CompHausFiltPseuNormGrp₁.{u u} r) ⟶
  (real_measures.functor.{u} p) :=
{ app := λ S, Θ p S,
  naturality' := λ S T f, by { ext x t, apply θ_natural, } }
.

def Θ_profinite : laurent_measures.functor.{u} r ⟶ real_measures.profinite.{u} p :=
Profinite.extend_nat_trans (Θ_fintype_nat_trans.{u} p)
.

set_option pp.universes true

variables (S : Profinite.{u})

#check Θ_fintype_nat_trans.{u}

#check (condensed r).obj S

#check CompHausFiltPseuNormGrp₁.to_Condensed.{u}

#check (real_measures.condensed p).obj S

def Θ_condensed_nat_trans :
  condensed r ⟶ real_measures.condensed p :=
whisker_right (Θ_profinite p) (CompHausFiltPseuNormGrp₁.to_Condensed)

def Θ_condensed (S : Profinite.{u}) :
  (condensed r).obj S ⟶ (real_measures.condensed p).obj S :=
(Θ_condensed_nat_trans p).app S

end laurent_measures
