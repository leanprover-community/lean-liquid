import toric.scattered_defs
import toric.pointed
import toric.pairing_dual_saturated

/-! In the intended application, these are the players:
* `R = ℕ`;
* `S = ℤ`;
* `M`and `N` are free finitely generated `ℤ`-modules that are dual to each other;
* `P = ℤ` is the target of the natural pairing `M ⊗ N → ℤ`.
-/

variables {R S M : Type*} [comm_semiring R]

variables [add_comm_monoid M] [semimodule R M]

namespace submodule

variables [semiring S] [algebra R S] [semimodule S M] [is_scalar_tower R S M]

/--  Hopefully, this lemma will be easy to prove. -/
lemma sup_extremal_rays {s : submodule R M} (sp : s.pointed S) :
  (⨆ r ∈ s.extremal_rays, r) = s :=
begin
  refine le_antisymm (bsupr_le $ λ i hi, hi.1) _,
  intros m ms t ht,
  rcases ht with ⟨y, rfl⟩,
  simp only [forall_apply_eq_imp_iff', supr_le_iff, set.mem_range, set_like.mem_coe, set.mem_Inter,
    set.mem_set_of_eq, exists_imp_distrib],
  intros a,
  rcases sp with ⟨el, lo⟩,
  sorry
end

end submodule


namespace pairing

variables [comm_semiring S] [algebra R S] [semimodule S M] [is_scalar_tower R S M]

variables {N P : Type*}
  [add_comm_monoid N] [semimodule R N] [semimodule S N] [is_scalar_tower R S N]
  [add_comm_monoid P] [semimodule R P] [semimodule S P] [is_scalar_tower R S P]
  (P₀ : submodule R P)

variables (f : pairing S M N P)

/--  The rays of the dual of the set `s` are the duals of the subsets of `s` that happen to be
cyclic. -/
def dual_set_rays (s : set M) : set (submodule R N) :=
{ r | r.is_cyclic ∧ ∃ s' ⊆ s, r = f.dual_set P₀ s' }

/-  We may need extra assumptions for this. -/
/--  The link between the rays of the dual and the extremal rays of the dual should be the
crucial finiteness step: if `s` is finite, there are only finitely many `dual_set_rays`, since
there are at most as many as there are subsets of `s`.  If the extremal rays generate
dual of `s`, then we are in a good position to prove Gordan's lemma! -/
lemma dual_set_rays_eq_extremal_rays (s : set M) :
  f.dual_set_rays P₀ s = (f.dual_set P₀ s).extremal_rays :=
sorry

lemma dual_set_pointed (s : set M) (hs : (submodule.span R s).saturation) :
  (f.dual_set P₀ s).pointed S := sorry

open submodule

lemma of_non_deg {M ι : Type*} [add_comm_group M] {f : pairing ℤ M M ℤ} {v : ι → M}
  (nd : perfect f) (sp : submodule.span ℤ (v '' set.univ)) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
begin
--  tidy?,
  sorry
end

lemma dual_dual_of_saturated {s : submodule R M} (ss : s.saturated) :
  f.flip.dual_set P₀ (f.dual_set P₀ s) = s :=
begin
  refine le_antisymm _ (subset_dual_dual f),
  intros m hm,
--  rw mem_dual_set at hm,
  change ∀ (n : N), n ∈ (dual_set P₀ f ↑s) → f m n ∈ P₀ at hm,
  simp_rw mem_dual_set at hm,
  -- is this true? I (KMB) don't know and the guru (Damiano) has left!
  -- oh wait, no way is this true, we need some nondegeneracy condition
  -- on f, it's surely not true if f is just the zero map.
  -- I (DT) think that you are right, Kevin.  We may now start to make assumptions
  -- that are more specific to our situation.
  sorry,
end

end pairing
