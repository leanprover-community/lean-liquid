import examples.Radon.defs

open_locale nnreal big_operators classical

noncomputable theory

open category_theory
open category_theory.limits
open topological_space

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space

namespace Profinite

def Radon_LC_to_fun (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon_LC p c → locally_constant X ℝ → ℝ :=
λ μ, μ.1

lemma Radon_LC_to_fun_injective (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  function.injective (X.Radon_LC_to_fun p c) :=
begin
  intros a b h, ext x : 2,
  exact congr_fun h x
end

lemma Radon_LC_to_fun_continuous (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  continuous (X.Radon_LC_to_fun p c) :=
begin
  apply continuous_pi,
  intros f,
  refine continuous.comp (weak_dual.eval_continuous f) (continuous_subtype_coe),
end

--WHY!?!?!?
instance t2_space_LC_to_R (X : Profinite.{0}) :
  t2_space (locally_constant X ℝ → ℝ) :=
@Pi.t2_space (locally_constant X ℝ) (λ _, ℝ) infer_instance
begin
  intros a, dsimp,
  apply_instance
end

instance t2_space_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  t2_space (X.Radon_LC p c) :=
⟨λ f g h, separated_by_continuous (X.Radon_LC_to_fun_continuous p c)
  $ (X.Radon_LC_to_fun_injective p c).ne h⟩

def Radon_LC_comparison (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.diagram ⋙ Radon_LC_functor p c ≅
  X.fintype_diagram ⋙ real_measures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c ⋙
  CompHaus_to_Top := sorry

end Profinite
