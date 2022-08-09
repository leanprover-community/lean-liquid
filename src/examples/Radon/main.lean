import examples.Radon.LC_limit

open_locale nnreal big_operators classical

noncomputable theory

open category_theory
open category_theory.limits
open topological_space

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space

namespace Profinite

def weak_dual_C_equiv_LC (X : Profinite.{0}) :
  weak_dual ℝ C(X,ℝ) ≃ₗ[ℝ] weak_dual ℝ (locally_constant X ℝ) :=
{ inv_fun := X.weak_dual_LC_to_C,
  left_inv := begin
    intros f, ext t,
    dsimp [weak_dual_C_to_LC, weak_dual_LC_to_C],
    apply (locally_constant.pkg X ℝ).induction_on t,
    { apply is_closed_eq,
      apply (locally_constant.pkg X ℝ).continuous_extend,
      apply_instance,
      apply f.2 },
    { intros e,
      rw (locally_constant.pkg X ℝ).extend_coe, refl,
      apply continuous_linear_map.uniform_continuous,
      apply_instance }
  end,
  right_inv := begin
    intros f, ext t,
    dsimp [weak_dual_C_to_LC, weak_dual_LC_to_C,
      weak_dual.comap],
    erw (locally_constant.pkg X ℝ).extend_coe,
    apply continuous_linear_map.uniform_continuous,
    apply_instance,
  end,
  ..(X.weak_dual_C_to_LC) }

def Radon_to_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)]:
  X.Radon p c ⟶ X.Radon_LC p c :=
{ to_fun := λ μ, ⟨weak_dual_C_to_LC _ μ.1, μ.2⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    exact continuous_linear_map.continuous _,
  end }

def Radon_LC_to_Radon (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)]:
  X.Radon_LC p c → X.Radon p c :=
λ μ, ⟨weak_dual_LC_to_C _ μ.1, begin
    change (weak_dual_C_to_LC _ (weak_dual_LC_to_C _ μ.1)).bdd_LC p c,
    erw X.weak_dual_C_equiv_LC.apply_symm_apply,
    exact μ.2,
  end⟩

instance compact_space_Radon (X : Profinite) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  compact_space (X.Radon p c) := sorry

def Radon_equiv_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon p c ≃ X.Radon_LC p c :=
{ to_fun := X.Radon_to_Radon_LC p c,
  inv_fun := X.Radon_LC_to_Radon p c,
  left_inv := begin
    intros t, ext1,
    apply X.weak_dual_C_equiv_LC.symm_apply_apply,
  end,
  right_inv := begin
    intros t, ext1,
    apply X.weak_dual_C_equiv_LC.apply_symm_apply,
  end }

lemma continuous_Radon_equiv_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  continuous (X.Radon_equiv_Radon_LC p c) :=
continuous_map.continuous _

lemma continuous_Radon_equiv_Radon_LC_symm (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  continuous (X.Radon_equiv_Radon_LC p c).symm :=
begin
  rw continuous_iff_is_closed,
  intros T hT,
  rw ← equiv.image_eq_preimage,
  apply is_compact.is_closed,
  apply is_compact.image,
  exact is_closed.is_compact hT,
  exact continuous_map.continuous _,
end

def Radon_homeomorph_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon p c ≃ₜ X.Radon_LC p c :=
{ continuous_to_fun := continuous_Radon_equiv_Radon_LC _ _ _,
  continuous_inv_fun := continuous_Radon_equiv_Radon_LC_symm _ _ _,
  ..(X.Radon_equiv_Radon_LC p c) }

def Radon_iso_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon p c ≅ X.Radon_LC p c :=
Top.iso_of_homeo (X.Radon_homeomorph_Radon_LC p c)

def Radon_functor_iso_Radon_LC_functor (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  Radon_functor p c ≅ Radon_LC_functor p c :=
nat_iso.of_components
(λ X, X.Radon_iso_Radon_LC p c)
sorry

end Profinite
