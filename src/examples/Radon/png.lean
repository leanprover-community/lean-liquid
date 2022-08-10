import examples.Radon.main

open_locale nnreal big_operators classical

noncomputable theory

open category_theory
open category_theory.limits
open topological_space

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space


namespace Profinite

variables (X : Profinite.{0}) (p : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)]

instance why_do_I_need_this : add_comm_group (weak_dual ℝ C(X,ℝ)) :=
show add_comm_group (C(X,ℝ) →L[ℝ] ℝ), by apply_instance

lemma bdd_add {ca cb} (a b : weak_dual ℝ C(X,ℝ)) (ha : a.bdd p ca) (hb : b.bdd p cb) :
  (a + b).bdd p (ca + cb) := sorry

lemma bdd_zero : (0 : weak_dual ℝ C(X,ℝ)).bdd p 0 := sorry

lemma bdd_neg {c} (a : weak_dual ℝ C(X,ℝ)) (ha : a.bdd p c) : (-a).bdd p c := sorry

def bdd_weak_dual : add_subgroup (weak_dual ℝ C(X,ℝ)) :=
{ carrier := { μ | ∃ c, μ.bdd p c },
  add_mem' := λ a b ha hb, begin
    obtain ⟨ca, ha⟩ := ha,
    obtain ⟨cb, hb⟩ := hb,
    use ca + cb,
    apply bdd_add _ _ _ _ ha hb,
  end,
  zero_mem' := ⟨0, bdd_zero _ _⟩,
  neg_mem' := λ a ha, begin
    obtain ⟨c,ha⟩ := ha,
    use c,
    apply bdd_neg _ _ _ ha,
  end }

instance : pseudo_normed_group (X.bdd_weak_dual p) :=
{ filtration := λ c, {μ | μ.1.bdd p c},
  filtration_mono := λ c₁ c₂ h μ hμ e, by apply le_trans (hμ e) h,
  zero_mem_filtration := λ c e, le_trans (bdd_zero _ _ _) (zero_le _),
  neg_mem_filtration := λ c μ hμ e, bdd_neg _ _ _ hμ _,
  add_mem_filtration := λ c₁ c₂ a b ha hb, bdd_add _ _ _ _ ha hb }

instance topological_space_bdd_weak_dual_filtration (c : ℝ≥0) :
  topological_space (pseudo_normed_group.filtration (X.bdd_weak_dual p) c) :=
topological_space.induced (λ μ, μ.1.1) infer_instance

def bdd_weak_dual_filtration_homeo (c : ℝ≥0) :
  (pseudo_normed_group.filtration (X.bdd_weak_dual p) c) ≃ₜ
  X.Radon p c :=
{ to_fun := λ μ, ⟨μ.1.1, μ.2⟩,
  inv_fun := λ μ, ⟨⟨μ.1, ⟨c, μ.2⟩⟩, μ.2⟩,
  left_inv := λ μ, by { ext, refl },
  right_inv := λ μ, by { ext, refl },
  continuous_to_fun := sorry,
  continuous_inv_fun := sorry }

instance : comphaus_filtered_pseudo_normed_group (X.bdd_weak_dual p) :=
{ t2 := λ c, (X.bdd_weak_dual_filtration_homeo p c).symm.t2_space,
  compact := λ c, (X.bdd_weak_dual_filtration_homeo p c).symm.compact_space,
  continuous_add' := sorry,
  continuous_neg' := sorry,
  continuous_cast_le := sorry,
  ..(infer_instance : pseudo_normed_group (X.bdd_weak_dual p)) }

def Radon_png (X : Profinite.{0}) (p : ℝ≥0)
  [fact (0 < p)] [fact (p ≤ 1)] : CompHausFiltPseuNormGrp₁ :=
{ M := X.bdd_weak_dual p,
  exhaustive' := λ μ, μ.2 }

end Profinite
