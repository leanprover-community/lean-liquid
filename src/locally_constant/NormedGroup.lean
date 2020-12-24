import locally_constant.analysis
import NormedGroup

noncomputable theory

set_option pp.proofs true

-- feel free to golf!!
lemma real.Sup_mul (r : ℝ) (s : set ℝ) (hr : 0 < r) :
  Sup ({x | ∃ y ∈ s, r * y = x}) = r * Sup s :=
begin
  let P₁ : Prop := (∃ (x : ℝ), x ∈ {x : ℝ | ∃ (y : ℝ) (H : y ∈ s), r * y = x}) ∧
    ∃ (x : ℝ), ∀ (y : ℝ), y ∈ {x : ℝ | ∃ (y : ℝ) (H : y ∈ s), r * y = x} → y ≤ x,
  let P₂ : Prop := (∃ (x : ℝ), x ∈ s) ∧ ∃ (x : ℝ), ∀ (y : ℝ), y ∈ s → y ≤ x,
  have H : P₁ ↔ P₂ := _,
  { by_cases h : P₁,
    { apply le_antisymm,
      { rw real.Sup_le _ h.1 h.2,
        rintro _ ⟨x, hx, rfl⟩,
        apply mul_le_mul_of_nonneg_left _ hr.le,
        rw H at h,
        exact real.le_Sup _ h.2 hx },
      { rw H at h,
        rw [← le_div_iff' hr, real.Sup_le _ h.1 h.2],
        intros x hx,
        rw le_div_iff' hr,
        rw ← H at h,
        exact real.le_Sup _ h.2 ⟨_, hx, rfl⟩ } },
    { simp only [real.Sup_def],
      classical,
      rw [dif_neg, dif_neg, mul_zero],
      { rw H at h, exact h }, { exact h } } },
  { apply and_congr,
    { simp only [exists_prop, set.mem_set_of_eq],
      rw exists_comm,
      simp only [and_comm, exists_eq_left'] },
    { simp only [exists_prop, set.mem_set_of_eq, and_comm],
      simp only [exists_eq_left', mul_comm r, ← div_eq_iff_mul_eq hr.ne.symm],
      split; rintro ⟨x, hx⟩,
      { refine ⟨x / r, λ y hy, _⟩,
        rw ← mul_div_cancel y hr.ne.symm at hy,
        rw le_div_iff hr,
        exact hx _ hy },
      { refine ⟨r * x, λ y hy, _⟩,
        rw ← div_le_iff' hr,
        exact hx _ hy } } },
end

namespace NormedGroup

local attribute [instance] locally_constant.normed_group locally_constant.metric_space

@[simps]
def LocallyConstant (S : Type*) [topological_space S] [compact_space S] :
  NormedGroup ⥤ NormedGroup :=
{ obj := λ V, NormedGroup.of $ locally_constant S V,
  map := λ V W f,
  { to_fun := locally_constant.map f,
    map_zero' := by { ext, exact f.map_zero' },
    map_add' := by { intros x y, ext s, apply f.map_add' },
    bound' :=
    begin
      obtain ⟨C, C_pos, hC⟩ := f.bound,
      use C,
      rintro (g : locally_constant _ _),
      calc Sup (set.range (λ x, ∥f (g x)∥))
          ≤ Sup (set.range (λ x, C * ∥g x∥)) : _
      ... = C * Sup (set.range (λ x, ∥g x∥)) : _,
      { by_cases H : nonempty S, swap,
        { simp only [set.range_eq_empty.mpr H, real.Sup_empty] },
        apply real.Sup_le_ub,
        { obtain ⟨x⟩ := H, exact ⟨_, set.mem_range_self x⟩ },
        rintro _ ⟨x, rfl⟩,
        calc ∥f (g x)∥ ≤ C * ∥g x∥ : hC _
        ... ≤ Sup _ : real.le_Sup _ _ _,
        { apply real.Sup_exists_of_finite,
          rw [set.range_comp, set.range_comp],
          exact (g.range_finite.image _).image _ },
        { exact set.mem_range_self _ } },
      { convert real.Sup_mul C _ C_pos using 2,
        ext x,
        simp only [set.mem_range, exists_prop, set.set_of_mem_eq, exists_exists_eq_and],
        simp only [set.mem_set_of_eq] }
    end },
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }

end NormedGroup
