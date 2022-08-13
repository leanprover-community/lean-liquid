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

def Radon_to_fun (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon p c → C(X,ℝ) → ℝ :=
λ μ, μ.1

lemma Radon_LC_to_fun_injective (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  function.injective (X.Radon_LC_to_fun p c) :=
begin
  intros a b h, ext x : 2,
  exact congr_fun h x
end

lemma Radon_to_fun_injective (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  function.injective (X.Radon_to_fun p c) :=
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

lemma Radon_to_fun_continuous (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  continuous (X.Radon_to_fun p c) :=
begin
  apply continuous_pi,
  intros f,
  refine continuous.comp (weak_dual.eval_continuous f) (continuous_subtype_coe),
end

--WHY!?!?!?
instance t2_space_fun_to_R (X : Type*) :
  t2_space (X → ℝ) :=
@Pi.t2_space X (λ _, ℝ) infer_instance
begin
  intros a, dsimp,
  apply_instance
end

instance t2_space_Radon_LC (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  t2_space (X.Radon_LC p c) :=
⟨λ f g h, separated_by_continuous (X.Radon_LC_to_fun_continuous p c)
  $ (X.Radon_LC_to_fun_injective p c).ne h⟩

instance t2_space_Radon (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  t2_space (X.Radon p c) :=
⟨λ f g h, separated_by_continuous (X.Radon_to_fun_continuous p c)
  $ (X.Radon_to_fun_injective p c).ne h⟩

def Radon_LC_comparison_component_equiv_aux (X : Profinite.{0}) (p : ℝ≥0)
  (T : discrete_quotient X) :
  weak_dual ℝ (locally_constant (X.diagram.obj T) ℝ) ≃
  real_measures p (X.fintype_diagram.obj T) :=
{ to_fun := λ μ t,
    μ (clopens.indicator_LC $
      discrete_quotient.fibre ⊥ (discrete_quotient.equiv_bot t)),
  inv_fun := λ μ,
  { to_fun := λ e, ∑ t : T, μ t * e t,
    map_add' := begin
      intros x y,
      dsimp,
      simp only [mul_add, finset.sum_add_distrib],
    end,
    map_smul' := begin
      intros r e, dsimp,
      rw finset.mul_sum,
      simp_rw [← mul_assoc, mul_comm r],
    end,
    cont := begin
      apply continuous_finset_sum, intros t ht,
      refine continuous.comp (continuous_mul_left (μ t)) _,
      sorry
    end },
  left_inv := sorry,
  right_inv := sorry }

lemma bdd_LC_iff_comparison
  (X : Profinite.{0}) (T : discrete_quotient X) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)]
  (f : weak_dual ℝ (locally_constant (X.diagram.obj T) ℝ)) :
  f.bdd_LC p c ↔
  X.Radon_LC_comparison_component_equiv_aux p T f ∈
    pseudo_normed_group.filtration (real_measures p (X.fintype_diagram.obj T)) c :=
sorry

def Radon_LC_comparison_component_equiv
  (X : Profinite.{0}) (T : discrete_quotient X) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  Radon_LC (X.diagram.obj T) p c ≃
  pseudo_normed_group.filtration (real_measures p (X.fintype_diagram.obj T)) c :=
{ to_fun := λ μ, ⟨X.Radon_LC_comparison_component_equiv_aux p T μ.1,
    begin
      rw ← bdd_LC_iff_comparison, exact μ.2,
    end⟩,
  inv_fun := λ μ, ⟨(X.Radon_LC_comparison_component_equiv_aux p T).symm μ.1,
    begin
      have := μ.2,
      rw ← (X.Radon_LC_comparison_component_equiv_aux p T).apply_symm_apply μ.val at this,
      rw ← bdd_LC_iff_comparison at this,
      exact this,
    end⟩,
  left_inv := begin
    intros μ, ext1,
    apply (X.Radon_LC_comparison_component_equiv_aux p T).symm_apply_apply,
  end,
  right_inv := begin
    intros μ, ext1,
    apply (X.Radon_LC_comparison_component_equiv_aux p T).apply_symm_apply,
  end }

lemma continuous_Radon_LC_comparison_component_equiv_symm
  (X : Profinite.{0}) (T : discrete_quotient X) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  continuous (X.Radon_LC_comparison_component_equiv T p c).symm :=
begin
  apply continuous_subtype_mk,
  apply weak_dual.continuous_of_continuous_eval,
  intros y,
  apply continuous_finset_sum,
  rintros t -,
  refine continuous.comp (continuous_mul_right (y t)) _,
  refine continuous.comp (continuous_apply t) continuous_subtype_coe,
end

def Radon_LC_comparison_component_homeo
  (X : Profinite.{0}) (T : discrete_quotient X) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  Radon_LC (X.diagram.obj T) p c ≃ₜ
  pseudo_normed_group.filtration (real_measures p (X.fintype_diagram.obj T)) c :=
{ continuous_to_fun := begin
    rw continuous_iff_is_closed, intros S hS,
    erw ← (Radon_LC_comparison_component_equiv _ _ _ _).symm.image_eq_preimage,
    apply is_compact.is_closed,
    apply hS.is_compact.image,
    apply continuous_Radon_LC_comparison_component_equiv_symm,
  end,
  continuous_inv_fun := continuous_Radon_LC_comparison_component_equiv_symm _ _ _ _,
  ..(X.Radon_LC_comparison_component_equiv T p c) }

def Radon_LC_comparison_component_iso
  (X : Profinite.{0}) (T : discrete_quotient X) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  Radon_LC (X.diagram.obj T) p c ≅
  Top.of (pseudo_normed_group.filtration (real_measures p (X.fintype_diagram.obj T)) c) :=
Top.iso_of_homeo $ Radon_LC_comparison_component_homeo _ _ _ _

lemma Radon_LC_comparison_naturality_aux (X : Profinite.{0})
  (S T : discrete_quotient X) (f : S ⟶ T) (t : T) (q : S) :
  ((⊥ : discrete_quotient T).fibre (discrete_quotient.equiv_bot t)).indicator_LC
    (X.fintype_diagram.map f q) =
  ∑ i : S in finset.univ.filter (λ j, X.fintype_diagram.map f j = t),
    ((⊥ : discrete_quotient S).fibre (discrete_quotient.equiv_bot i)).indicator_LC q :=
begin
  by_cases H : (X.fintype_diagram.map f q = t),
  { rw @finset.sum_eq_single ℝ S _
      (finset.filter (λ (j : (X.fintype_diagram.obj S).α),
        X.fintype_diagram.map f j = t) finset.univ)
      (λ i, ((⊥ : discrete_quotient S).fibre
        (discrete_quotient.equiv_bot i)).indicator_LC q) q _ _,
    { dsimp [clopens.indicator_LC, set.indicator, discrete_quotient.fibre],
      erw if_pos rfl,
      rw if_pos, congr' 1 },
    { intros s hs hsq, rw finset.mem_filter at hs,
      dsimp [clopens.indicator_LC, set.indicator, discrete_quotient.fibre],
      rw if_neg,
      contrapose! hsq,
      apply_fun discrete_quotient.equiv_bot.symm at hsq,
      rw equiv.symm_apply_apply at hsq,
      erw equiv.symm_apply_apply at hsq,
      exact hsq.symm },
    { intros hq,
      erw finset.mem_filter at hq,
      push_neg at hq, specialize hq (finset.mem_univ _),
      exact false.elim (hq H) } },
  { change ite _ _ _ = _, rw if_neg,
    { symmetry, apply finset.sum_eq_zero,
      intros s hs, rw finset.mem_filter at hs, replace hs := hs.2,
      change ite _ _ _ = _, rw if_neg,
      contrapose! H,
      dsimp [discrete_quotient.fibre] at H,
      apply_fun discrete_quotient.equiv_bot.symm at H,
      rw equiv.symm_apply_apply at H,
      erw equiv.symm_apply_apply at H,
      rw H, exact hs },
    { contrapose! H,
      dsimp [discrete_quotient.fibre] at H,
      apply_fun discrete_quotient.equiv_bot.symm at H,
      rw equiv.symm_apply_apply at H,
      erw equiv.symm_apply_apply at H,
      exact H } },
end

def Radon_LC_comparison (X : Profinite.{0}) (p c : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] :
  X.diagram ⋙ Radon_LC_functor p c ≅
  X.fintype_diagram ⋙ real_measures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c ⋙
  CompHaus_to_Top :=
nat_iso.of_components
(λ T, Radon_LC_comparison_component_iso _ _ _ _)
begin
  intros S T f,
  ext a t,
  dsimp [Radon_functor, Radon_LC_comparison_component_iso,
    Radon_LC_comparison_component_homeo,
    Radon_LC_comparison_component_equiv,
    Radon_LC_comparison_component_equiv_aux,
    Radon_LC_functor, real_measures.map_hom,
    CompHausFiltPseuNormGrp₁.level,
    map_Radon_LC, weak_dual.comap
    ],
  let aa : weak_dual ℝ (locally_constant S ℝ) := a.1,
  erw ← aa.map_sum,
  congr' 1,
  ext q,
  rw locally_constant.sum_apply,
  dsimp [continuous_map.comap_LC],
  convert Radon_LC_comparison_naturality_aux X S T f t q,
end

end Profinite
