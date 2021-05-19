import for_mathlib.SemiNormedGroup
import algebra.homology.additive
import locally_constant.Vhat
import normed_group.controlled_exactness

noncomputable theory

variables (C : cochain_complex SemiNormedGroup ℕ)

open SemiNormedGroup

/-- The completed cochain complex associated to C. -/
abbreviation cmpl := (Completion.map_homological_complex _).obj C

open_locale nnreal

lemma cmpl_exact_of_exact (ε : ℝ≥0) (hε : 0 < ε)
  (cond : ∀ (n : ℕ) (f : C.X (n+1)) (hf : C.d (n+1) (n+2) f = 0),
    ∃ g : C.X n, C.d _ _ g = f ∧ (nnnorm g) ≤ (nnnorm f)) (n : ℕ) (f : (cmpl C).X (n+1))
    (hf : (cmpl C).d _ (n+2) f = 0) : ∃ g : (cmpl C).X n, (cmpl C).d _ _ g = f ∧
    (nnnorm g) ≤ (1 + ε) * (nnnorm f) :=
begin
  have := @controlled_exactness (C.X (n+1)) (C.X n) (C.X (n+2)) _ _ _ (C.d _ _) 1 zero_lt_one
    1 (C.d _ _) _ _ f _ ε hε,
  { rcases this with ⟨g,hg1,hg2⟩,
    exact ⟨g,hg1,hg2⟩ },
  { intros g hg,
    erw add_monoid_hom.mem_ker at hg,
    specialize cond _ g hg,
    rcases cond with ⟨g',h1,h2⟩,
    refine ⟨g',h1,_⟩,
    simpa },
  { rintros g ⟨g,rfl⟩,
    specialize cond (n+1) (C.d (n+1) (n+2) g) _,
    { change (C.d (n+1) (n+2) ≫ C.d (n+2) (n+3)) g = 0,
      simp },
    rcases cond with ⟨g',h1,h2⟩,
    refine ⟨g',h1,_⟩,
    dsimp,
    simp,
    exact h2 },
  { erw add_monoid_hom.mem_ker,
    exact hf },
end
