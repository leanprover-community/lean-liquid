import pseudo_normed_group.basic

noncomputable theory

local attribute [instance] type_pow

open_locale nnreal big_operators

namespace pseudo_normed_group

instance finsupp (ι M : Type*) [pseudo_normed_group M] : pseudo_normed_group (ι →₀ M) :=
{ filtration := λ c, { f | ∃ γ : ι →₀ ℝ≥0, γ.sum (λ i, id) ≤ c ∧ ∀ i, f i ∈ filtration M (γ i) },
  filtration_mono := λ c₁ c₂ h, by { rintro f ⟨γ, hγ, hf⟩, exact ⟨γ, hγ.trans h, hf⟩, },
  zero_mem_filtration := λ c, ⟨0, by simp, λ i, zero_mem_filtration _⟩,
  neg_mem_filtration := λ c, by { rintro f ⟨γ, hγ, hf⟩, exact ⟨γ, hγ, λ i, neg_mem_filtration (hf i)⟩, },
  add_mem_filtration := λ c₁ c₂, begin
    rintro f₁ f₂ ⟨γ₁, hγ₁, hf₁⟩ ⟨γ₂, hγ₂, hf₂⟩,
    refine ⟨γ₁ + γ₂, _, _⟩,
    { rw [finsupp.sum_add_index'],
      { exact add_le_add hγ₁ hγ₂ },
      { intro, refl },
      { intros, refl } },
    { intro, exact add_mem_filtration (hf₁ _) (hf₂ _) }
  end }

end pseudo_normed_group
