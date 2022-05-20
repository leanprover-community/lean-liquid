import for_mathlib.bicartesian3

noncomputable theory

universe u

open category_theory

-- jmc: feel free to generalize to arbitrary abelian cats
-- also, my apologies for `α = -𝟙 _`...
-- it might be worthwile to first prove an aux-lemma with `= 𝟙 _` and then negate all maps

-- SELFCONTAINED
lemma bicartesian_of_id_of_end_of_end_of_id
  {A B C D : Ab.{u}} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
  {α : A ⟶ A} {β : B ⟶ B} {γ : C ⟶ C} {δ : D ⟶ D}
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
