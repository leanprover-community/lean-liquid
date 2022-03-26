import analysis.specific_limits.basic
import category_theory.Fintype
import analysis.normed_space.basic

import pseudo_normed_group.basic
import pseudo_normed_group.category

universe u

noncomputable theory
open_locale big_operators nnreal classical
open set

structure invpoly_bdd (r : ℝ≥0) (S : Fintype) (T : finset ℕ) (c : ℝ≥0) :=
(to_fun : S → T → ℤ)
(bound' : ∑ s i, ∥to_fun s i∥₊ * r ^ (-i : ℤ) ≤ c)

namespace invpoly_bdd

variables {r : ℝ≥0} {S S' S'' : Fintype.{u}} {T : finset ℕ} {c : ℝ≥0}

instance : has_coe_to_fun (invpoly_bdd r S T c) (λ _, S → T → ℤ) :=
⟨λ F, F.1⟩

@[ext] lemma ext (F G : invpoly_bdd r S T c) :
  (F : S → T → ℤ) = G  → F = G := by {intros h, cases F, cases G, simpa }

instance : has_nnnorm (invpoly_bdd r S T c) :=
⟨λ F, ∑ s i, ∥F s i∥₊ * r^(-i : ℤ)⟩

@[simp] lemma nnnorm_def (F : invpoly_bdd r S T c) :
  ∥F∥₊ = ∑ s i, ∥F s i∥₊ * r^(-i : ℤ) := rfl

lemma bound (F : invpoly_bdd r S T c) : ∥F∥₊ ≤ c := F.2

def map (f : S ⟶ S') : invpoly_bdd r S T c → invpoly_bdd r S' T c := λ F,
{ to_fun := λ s' k, ∑ s in finset.univ.filter (λ t, f t = s'), F s k,
  bound' := calc
  ∑ (s : S') (i : T),
    ∥∑ (s : S.α) in finset.univ.filter (λ (t : S), f t = s), F s i∥₊ * r^(-i : ℤ) ≤
  ∑ (s' : S') (i : T), ∑ s in finset.univ.filter (λ t, f t = s'), ∥F s i∥₊ * r^(-i : ℤ) :
  begin
    apply finset.sum_le_sum,
    intros s' hs',
    apply finset.sum_le_sum,
    intros i hi,
    rw ← finset.sum_mul,
    exact mul_le_mul' (nnnorm_sum_le _ _) (le_refl _)
  end
  ... =
    ∑ (s' : S'), ∑ s in finset.univ.filter (λ t, f t = s'), ∑ i, ∥F s i∥₊ * r^(-i : ℤ) :
  begin
    apply finset.sum_congr rfl,
    intros s' hs',
    rw finset.sum_comm,
  end
  ... = ∑ s, ∑ i, ∥F s i∥₊ * r^(-i : ℤ) :
  begin
    rw ← finset.sum_bUnion,
    { apply finset.sum_congr,
      { ext e,
        split,
        { simp },
        { intro h,
          simp only [true_and, finset.mem_univ,
            finset.mem_bUnion, exists_true_left, finset.mem_filter],
          use f e } },
      { tauto } },
    { intros x hx y hy h i hi,
      apply h,
      simp at hi,
      rw [← hi.1, ← hi.2] }
  end
  ... ≤ c : F.bound }

@[simp]
lemma map_apply (f : S ⟶ S') (F : invpoly_bdd r S T c) (s' : S') (t : T) :
  map f F s' t = ∑ s in finset.univ.filter (λ i, f i = s'), F s t := rfl

@[simp]
lemma map_id : (map (𝟙 S) : invpoly_bdd r S T c → invpoly_bdd r S T c) = id :=
begin
  ext F s t,
  dsimp,
  change ∑ s in finset.univ.filter (λ i, i = s), F s t = _,
  simp [finset.sum_filter],
end

@[simp]
lemma map_comp (f : S ⟶ S') (g : S' ⟶ S'') :
  (map (f ≫ g) : invpoly_bdd r S T c → invpoly_bdd r S'' T c) = map g ∘ map f :=
begin
  ext F s t,
  simp,
  rw ← finset.sum_bUnion,
  { apply finset.sum_congr,
    { ext x,
      split,
      { intro h, simpa using h },
      { intro h, simpa using h } },
    { tauto } },
  { intros i hi j hj h e he,
    simp at he,
    apply h,
    rw [← he.1, ← he.2] }
end

lemma coeff_bound (F : invpoly_bdd r S T c) [hr : fact (0 < r)]
  (s : S) (i : T) : ∥F s i∥₊ ≤ c * (r^(-i : ℤ))⁻¹ :=
begin
  suffices : ∥F s i∥₊ * r^(-i : ℤ) ≤ c,
  { convert mul_le_mul' this le_rfl using 1,
    have hh : 0 < (r^(-i : ℤ))⁻¹,
    { rw [nnreal.inv_pos], exact nnreal.zpow_pos hr.out.ne' _, },
    rw mul_inv_cancel_right₀,
    exact zpow_ne_zero _ hr.out.ne', },
  calc ∥F s i∥₊ * r ^ (-i:ℤ)
      ≤ ∑ i, ∥F s i∥₊ * r ^ (-i:ℤ) : @finset.single_le_sum T _ _ (λ i, ∥F s i∥₊ * r^(-i:ℤ)) _ _ _ _
  ... ≤ ∥F∥₊ : @finset.single_le_sum S _ _ (λ s, ∑ i, ∥F s i∥₊ * r^(-i:ℤ)) _ _ _ _
  ... ≤ c : F.bound,
  all_goals { exact finset.mem_univ _ <|> { intros, exact zero_le' } }
end

open_locale classical

instance (r : ℝ≥0) [fact (0 < r)] (S : Fintype) (T : finset ℕ) :
  fintype (invpoly_bdd r S T c) :=
begin
  let lb : T → ℤ := λ i, int.floor (-((c : ℝ) * ((r : ℝ)^(-i : ℤ))⁻¹)),
  let ub : T → ℤ := λ i, int.ceil ((c : ℝ) * ((r : ℝ)^(-i : ℤ))⁻¹),
  let ι : invpoly_bdd r S T c →
    (Π (s : S) (i : T), Icc (lb i) (ub i)) :=
    λ F s i, ⟨F s i, _⟩,
  apply fintype.of_injective ι _,
  { intros F G h,
    ext s i,
    apply_fun (λ e, (e s i : ℤ)) at h,
    exact h },
  { have := F.coeff_bound s i,
    change (abs (F s i) : ℝ) ≤ _ at this,
    simp only [abs_le, nnreal.coe_mul, nnreal.coe_inv, nnreal.coe_zpow] at this,
    split,
    { replace := le_trans (int.floor_le _) this.1,
      rwa int.cast_le at this, },
    { replace := le_trans this.2 (int.le_ceil _),
      rwa int.cast_le at this, } }
end

instance : topological_space (invpoly_bdd r S T c) := ⊥

example [fact (0 < r)] : compact_space (invpoly_bdd r S T c) :=
  by apply_instance

example : t2_space (invpoly_bdd r S T c) := by apply_instance

example : totally_disconnected_space (invpoly_bdd r S T c) :=
  by apply_instance

end invpoly_bdd
