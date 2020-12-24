import locally_constant.analysis
import NormedGroup

noncomputable theory

lemma real.Sup_mul (r : ℝ) (s : set ℝ) (hr : 0 ≤ r) :
  Sup ({x | ∃ y ∈ s, r * y = x}) = r * Sup s :=
begin
  sorry
end

namespace NormedGroup

local attribute [instance] locally_constant.normed_group locally_constant.metric_space

set_option pp.all true

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
        { refine ⟨x, _⟩,
          -- refl doesn't want to close the goal :shock:
          dsimp [NormedGroup], refl } },
      { convert real.Sup_mul C _ C_pos,
        ext,
        simp only [exists_prop, set.mem_range, exists_exists_eq_and, set.mem_set_of_eq], }
    end } }

end NormedGroup
