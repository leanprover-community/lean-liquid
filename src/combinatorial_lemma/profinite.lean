import Mbar.functor
import combinatorial_lemma.finite

import category_theory.limits.preserves.finite

noncomputable theory

open_locale nnreal big_operators

universe u

section
variables (r : ℝ≥0) [fact (0 < r)] (Λ : Type u) [polyhedral_lattice Λ]

def foo (M : Type*) [profinitely_filtered_pseudo_normed_group_with_Tinv r M] :
  profinitely_filtered_pseudo_normed_group_with_Tinv r (Λ →+ M) :=
  by apply_instance

#check polyhedral_lattice.add_monoid_hom.profinitely_filtered_pseudo_normed_group_with_Tinv
#print foo

-- NOTE: We can use the commented out proofs.
def hom_functor : ProFiltPseuNormGrpWithTinv₁.{u} r ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r :=
{ obj := λ M,
  { M := Λ →+ M,
    str := infer_instance,
    exhaustive' := begin
      /-
      intros m,
      obtain ⟨ι,hι,l,hl,h⟩ := polyhedral_lattice.polyhedral Λ,
      resetI,
      have := ProFiltPseuNormGrpWithTinv₁.exhaustive r,
      let cs : ι → ℝ≥0 := λ i, (M.exhaustive r (m (l i))).some,
      -- This should be easy, using the fact that (l i) ≠ 0.
      have : ∃ c : ℝ≥0, ∀ i, cs i ≤ c * ∥l i∥₊, sorry,
      obtain ⟨c,hc⟩ := this,
      use c,
      rw generates_norm.add_monoid_hom_mem_filtration_iff hl m,
      intros i,
      apply pseudo_normed_group.filtration_mono (hc i),
      apply (M.exhaustive r (m (l i))).some_spec,
      -/
      sorry
    end },
  map := λ M N f,
  { to_fun := λ m, f.to_add_monoid_hom.comp m,
    map_zero' := sorry, -- by simp,
    map_add' := λ _ _, sorry, --by { ext, simp },
    strict' := begin
      /-
      intros c m hm,
      obtain ⟨ι,hι,l,hl,h⟩ := polyhedral_lattice.polyhedral Λ,
      resetI,
      erw generates_norm.add_monoid_hom_mem_filtration_iff hl at hm ⊢,
      intros i,
      dsimp,
      apply f.strict,
      apply hm,
      -/
      sorry
    end,
    continuous' := sorry,
    map_Tinv' := sorry },
  map_id' := λ M, sorry, -- by { ext, dsimp, simp },
  map_comp' := λ M N L f g, sorry -- by { ext, dsimp, simp }
}

open category_theory.limits

--instance : preserves_finite_limits (hom_functor r Λ ⋙ ProFiltPseuNormGrpTinv₁) := sorry

end

/-- Lemma 9.8 of [Analytic] -/
lemma lem98 (r' : ℝ≥0) [fact (0 < r')] [fact (r' < 1)]
  (Λ : Type*) [polyhedral_lattice Λ] (S : Profinite) (N : ℕ) [hN : fact (0 < N)] :
  pseudo_normed_group.splittable (Λ →+ (Mbar.functor r').obj S) N (lem98.d Λ N) :=
begin
  -- This reduces to `lem98_finite`: See the first lines of the proof in [Analytic].
  sorry
end
