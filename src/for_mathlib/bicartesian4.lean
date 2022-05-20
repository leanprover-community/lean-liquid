import for_mathlib.bicartesian3

noncomputable theory

universe u

open category_theory category_theory.limits


section part1

-- jmc: feel free to generalize to arbitrary abelian cats
variables {A B C D : Ab.{u}} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
variables {α : A ⟶ A} {β : B ⟶ B} {γ : C ⟶ C} {δ : D ⟶ D}

-- jmc: my apologies for the `α = -𝟙 _` assumption below...
-- it might be worthwile to first prove an aux-lemma with `= 𝟙 _` and then negate all maps

-- SELFCONTAINED
lemma bicartesian_of_id_of_end_of_end_of_id
  (H : exact_seq Ab.{u} [f, g, h])
  (sq1 : commsq f α β f) (sq2 : commsq g β γ g) (sq3 : commsq h γ δ h)
  (hα : α = -𝟙 _) (hδ : δ = -𝟙 _) :
  sq2.bicartesian :=
begin
  have aux : _ := _,
  rw commsq.bicartesian_iff_isos _ _ aux aux sq2.kernel sq2 sq2.cokernel,
  swap,
  { apply exact.cons, { exact exact_kernel_ι },
    apply exact.exact_seq, { apply abelian.exact_cokernel } },
  sorry
  -- use (important!) the fact that we have a `kernel.map` (resp. `cokernel.map`)
  -- arising between two identical exact sequences
end

end part1

section part2

-- jmc: this part does not depend on the first section,
-- it's the same file because two lemmas have the same theme

-- jmc: feel free to generalize to arbitrary abelian cats
variables {A₁₁ A₁₂ A₁₃ A₁₄ A₁₅ : Ab.{u}}
variables {A₂₁ A₂₂ A₂₃ A₂₄ A₂₅ : Ab.{u}}
-- horizontal maps are `f`s and vertical maps are `g`s
variables {f₁₁ : A₁₁ ⟶ A₁₂} {f₁₂ : A₁₂ ⟶ A₁₃} {f₁₃ : A₁₃ ⟶ A₁₄} {f₁₄ : A₁₄ ⟶ A₁₅}
variables {g₁₁ : A₁₁ ⟶ A₂₁} {g₁₂ : A₁₂ ⟶ A₂₂} {g₁₃ : A₁₃ ⟶ A₂₃} {g₁₄ : A₁₄ ⟶ A₂₄} {g₁₅ : A₁₅ ⟶ A₂₅}
variables {f₂₁ : A₂₁ ⟶ A₂₂} {f₂₂ : A₂₂ ⟶ A₂₃} {f₂₃ : A₂₃ ⟶ A₂₄} {f₂₄ : A₂₄ ⟶ A₂₅}

-- SELFCONTAINED
lemma iso_of_bicartesian_of_bicartesian
  (h_ex₁ : exact_seq Ab.{u} [f₁₁, f₁₂, f₁₃, f₁₄])
  (h_ex₂ : exact_seq Ab.{u} [f₂₁, f₂₂, f₂₃, f₂₄])
  (sq1 : commsq f₁₁ g₁₁ g₁₂ f₂₁) (sq2 : commsq f₁₂ g₁₂ g₁₃ f₂₂)
  (sq3 : commsq f₁₃ g₁₃ g₁₄ f₂₃) (sq4 : commsq f₁₄ g₁₄ g₁₅ f₂₄)
  (H1 : sq1.bicartesian) (H4 : sq4.bicartesian) :
  is_iso f₁₃ :=
sorry

-- SELFCONTAINED
lemma iso_of_zero_of_bicartesian
  (h_ex₁ : exact_seq Ab.{u} [f₁₂, f₁₃, f₁₄])
  (h_ex₂ : exact_seq Ab.{u} [f₂₂, f₂₃, f₂₄])
  (hz₁ : is_zero A₁₂) (hz₂ : is_zero A₂₂)
  (sq2 : commsq f₁₂ g₁₂ g₁₃ f₂₂) (sq3 : commsq f₁₃ g₁₃ g₁₄ f₂₃)
  (sq4 : commsq f₁₄ g₁₄ g₁₅ f₂₄) (H4 : sq4.bicartesian) :
  is_iso f₁₃ :=
-- apply `iso_of_bicartesian_of_bicartesian` and provide a zero square on the left
sorry

end part2
