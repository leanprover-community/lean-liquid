import topology.algebra.ordered
import toric_2021_02_19.scattered_defs
import toric_2021_02_19.is_inj_nonneg
import toric_2021_02_19.PR_made
import toric_2021_02_19.pointed
import toric_2021_02_19.pairing_dual_saturated

/-! In the intended application, these are the players:
* `R₀ = ℕ`;
* `R = ℤ`;
* `M`and `N` are free finitely generated `ℤ`-modules that are dual to each other;
* `P = ℤ` is the target of the natural pairing `M ⊗ N → ℤ`.
-/

open_locale big_operators classical

-- Here we make the general statements that require few assumptions on the various types.
section abstract

variables (R₀ R M : Type*) [comm_semiring R₀]

namespace submodule

variables {R₀} {M}

variables [semiring R] [algebra R₀ R]
  [add_comm_monoid M] [semimodule R₀ M] [semimodule R M] [is_scalar_tower R₀ R M]

/--  Hopefully, this lemma will be easy to prove. -/
lemma sup_extremal_rays {s : submodule R₀ M} (sp : s.pointed R) :
  (⨆ r ∈ s.extremal_rays, r) = s :=
begin
  refine le_antisymm (bsupr_le $ λ i hi, hi.1) _,
  intros m ms t ht,
  rcases ht with ⟨y, rfl⟩,
  simp only [forall_apply_eq_imp_iff', supr_le_iff, set.mem_range, mem_coe, set.mem_Inter,
    set.mem_set_of_eq, exists_imp_distrib],
  intros a,
  rcases sp with ⟨el, lo⟩,
  sorry
end

end submodule


namespace pairing

variables [comm_semiring R] [algebra R₀ R]
  [add_comm_monoid M] [semimodule R₀ M] [semimodule R M] [is_scalar_tower R₀ R M]

variables (N P : Type*)
  [add_comm_monoid N] [semimodule R₀ N] [semimodule R N] [is_scalar_tower R₀ R N]
  [add_comm_monoid P] [semimodule R₀ P] [semimodule R P] [is_scalar_tower R₀ R P]
  (P₀ : submodule R₀ P)

variables {R₀ R M N P}

variables (f : pairing R M N P)

/--  The rays of the dual of the set `s` are the duals of the subsets of `s` that happen to be
cyclic. -/
def dual_set_rays (s : set M) : set (submodule R₀ N) :=
{ r | r.is_cyclic ∧ ∃ s' ⊆ s, r = f.dual_set P₀ s' }

/-  We may need extra assumptions for this. -/
/--  The link between the rays of the dual and the extremal rays of the dual should be the
crucial finiteness step: if `s` is finite, there are only finitely many `dual_set_rays`, since
there are at most as many as there are subsets of `s`.  If the extremal rays generate
dual of `s`, then we are in a good position to prove Gordan's lemma! -/
lemma dual_set_rays_eq_extremal_rays (s : set M) :
  f.dual_set_rays P₀ s = (f.dual_set P₀ s).extremal_rays :=
sorry

lemma dual_set_pointed (s : set M) (hs : (submodule.span R₀ s).saturation) :
  (f.dual_set P₀ s).pointed R := sorry

open submodule

lemma of_non_deg {M : Type*} [add_comm_group M] {ι : Type*} {f : pairing ℤ M M ℤ} {v : ι → M}
  (nd : perfect f) (sp : submodule.span ℤ (v '' set.univ)) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
begin
--  tidy?,
  sorry
end

lemma dual_dual_of_saturated {S : submodule R₀ M} (Ss : S.saturated) :
  f.flip.dual_set P₀ (f.dual_set P₀ S) = S :=
begin
  refine le_antisymm _ (subset_dual_dual f),
  intros m hm,
--  rw mem_dual_set at hm,
  change ∀ (n : N), n ∈ (dual_set P₀ f ↑S) → f m n ∈ P₀ at hm,
  simp_rw mem_dual_set at hm,
  -- is this true? I (KMB) don't know and the guru (Damiano) has left!
  -- oh wait, no way is this true, we need some nondegeneracy condition
  -- on f, it's surely not true if f is just the zero map.
  -- I (DT) think that you are right, Kevin.  We may now start to make assumptions
  -- that are more specific to our situation.
  sorry,
end

end pairing

end abstract

-- ending the section to clear out all the assumptions

section concrete

/-! In the intended application, these are the players:
* `R₀ = ℕ`;
* `R = ℤ`;
* `M`and `N` are free finitely generated `ℤ`-modules that are dual to each other;
* `P = ℤ` is the target of the natural pairing `M ⊗ N → ℤ`.
-/

namespace pairing

open pairing submodule

variables {M : Type*} [add_comm_group M]

/-  Kevin's proof. -/
lemma finite.smul_of_finite {S M : Type*} [semiring S] [add_comm_monoid M] [semimodule S M]
  {G : set S} {v : set M} (fG : G.finite) (fv : v.finite) :
  (G • v).finite :=
fG.image2 (•) fv

lemma finite.span_restrict {R S : Type*} [semiring S]
  [comm_semiring R] [semimodule R M] [semimodule S M] [algebra R S]
  [is_scalar_tower R S M] {G : set S} {v : set M}
  (fG : G.finite) (spg : submodule.span R G = ⊤)
  (fv : v.finite) (hv : submodule.span S v = ⊤) :
  ∃ t : set M, t.finite ∧ submodule.span R (t : set M) = (span S (v : set M)).restrict_scalars R :=
⟨G • v, fG.image2 (•) fv, span_smul spg v⟩

lemma finset.span_restrict {R S : Type*} [semiring S]
  [comm_semiring R] [semimodule R M] [semimodule S M] [algebra R S]
  [is_scalar_tower R S M]
  (G : finset S) (spg : submodule.span R (G : set S) = ⊤)
  (v : finset M) (hv : submodule.span S (v : set M) = ⊤) :
  ∃ t : finset M, submodule.span R (t : set M) = (span S (v : set M)).restrict_scalars R :=
begin
  obtain ⟨t, ft, co⟩ := finite.span_restrict G.finite_to_set spg v.finite_to_set hv,
  haveI ff : fintype t := ft.fintype,
  refine ⟨t.to_finset, by simpa only [set.coe_to_finset]⟩
end


/--  The submodule spanned by a set `s` over an `R`-algebra `S` is spanned as an `R`-module by
`s ∪ - s`, if for every element `a ∈ S`, either `a` or `- a` is in the image of `R`. -/
lemma finset.restrict_inf_span {R S : Type*} [ordered_semiring S] [topological_space S]
  [order_topology S] [comm_semiring R] [semimodule R M] [semimodule S M] [algebra R S]
  [is_scalar_tower R S M]
  -- the `R`-algebra `S` is compactly generated as an `R`-module
  (G : set S) (cG : is_compact G) (spg : submodule.span R G = ⊤)
  -- `R` is discrete as an `S`-module
  -- this works well, for instance, in the case `ℤ ⊆ ℝ`.
  -- It does not apply in the case `ℚ ⊆ ℝ`
  (dR : discrete_topology (set.range (algebra_map R S)))
  -- the `R`-lattice structure on `M` is given by the span of the set `v`
  (v : set M) (hv : submodule.span S v = ⊤)
  -- a finitely generated `S`-submodule of `M` is also finitely generated over `R`.
  (s : finset M) (pro : finset S) :
  ∃ t : finset M, submodule.span R (t : set M) =
    ((submodule.span S (s : set M)).restrict_scalars R) ⊓ submodule.span R v :=
begin
  let GS : set S := (set.range (algebra_map R S)) ∩ G,
  haveI dGS : discrete_topology GS :=
    discrete_topology.of_subset dR ((set.range ⇑(algebra_map R S)).inter_subset_left G),
  have cGS : is_compact (set.univ : set GS), sorry,
  have GS_finite : (set.univ : set GS).finite := finite_of_is_compact_of_discrete set.univ cGS,
  set GSM : set M := (GS : set S) • (s : set M),
  have : GSM.finite,sorry,
  refine ⟨this.to_finset, _⟩,
  sorry,
/-
  -- con questo voglio concludere la finitezza
  --apply fintype_of_compact_of_discrete,
-/
end

/--  The submodule spanned by a set `s` over an `R`-algebra `S` is spanned as an `R`-module by
`s ∪ - s`, if for every element `a ∈ S`, either `a` or `- a` is in the image of `R`. -/
lemma subset.span_union_neg_self_eq {R S : Type*} [ordered_comm_ring S]
  [comm_semiring R] [semimodule R M] [module S M] [algebra R S] [is_scalar_tower R S M]
  (ff : ∀ a : S, ∃ n : R, a = algebra_map R S n ∨ a = - algebra_map R S n) (s : set M) :
  (submodule.span R (s ∪ - s)).carrier = submodule.span S (s : set M) :=
begin
  ext m,
  refine ⟨λ hm, _, λ hm, _⟩,
  { refine (span S (s : set M)).mem_coe.mpr _,
    rcases mem_span_set.mp hm with ⟨c, csup, rfl⟩,
    refine sum_mem _ (λ a as, (_ : c a • a ∈ span S s)),
    rw ← algebra_map_smul S (c a) a,
    refine smul_mem (span S s) _ _,
    obtain cams : a ∈ s ∪ - s := set.mem_of_mem_of_subset as csup,
    cases (set.mem_union a s _).mp cams,
    { exact subset_span h },
    { refine (neg_mem_iff _).mp (subset_span h) } },
  { rcases mem_span_set.mp hm with ⟨c, csup, rfl⟩,
    rw [mem_carrier, mem_coe],
    refine sum_mem _ (λ a as, (_ : c a • a ∈ span R (s ∪ - s))),
    rcases ff (c a) with ⟨ca, cap | can⟩,
    { rw [cap, algebra_map_smul],
      refine smul_mem _ ca _,
      refine subset_span (set.mem_union_left _ _),
      exact set.mem_of_mem_of_subset (finset.mem_coe.mpr as) csup },
    { rw [can, neg_smul, algebra_map_smul, ← smul_neg],
      refine smul_mem _ ca _,
      refine subset_span (set.mem_union_right _ _),
      rw [set.mem_neg, neg_neg],
      exact set.mem_of_mem_of_subset (finset.mem_coe.mpr as) csup } }
end


lemma finset.span_union_neg_self_eq {ι R S : Type*} [ordered_comm_ring S]
  [comm_semiring R] [semimodule R M] [module S M] [algebra R S] [is_scalar_tower R S M]
  (ff : ∀ s : S, ∃ n : R, s = algebra_map R S n ∨ s = - algebra_map R S n)
  {v : ι → M} (bv : is_basis S v) (s : finset M) (hRS : is_inj_nonneg (algebra_map R S)) :
  ∃ sR : finset M,
    (submodule.span R (sR : set M)).carrier = submodule.span S (s : set M) :=
begin
  classical,
  let ms : finset M := s.image (λ i, - i),
  refine ⟨s ∪ (s.image (λ i, - i)), _⟩,
  ext m,
  refine ⟨_, _⟩;intros hm,
  { refine (span S (s : set M)).mem_coe.mpr _,
    rcases mem_span_finset.mp hm with ⟨c, rfl⟩,
    refine sum_mem _ (λ a as, _),
    rw ← algebra_map_smul S (c a) a,
    refine smul_mem (span S (s : set M)) _ _,
    sorry,
/-
    cases finset.mem_union.mp as,
    have : a ∈ span S {a} := mem_span_singleton_self a,
    have asu : {a} ⊆ s := finset.singleton_subset_iff.mpr h,
    have : a ∈ (span S ↑s).carrier,refine set.mem_of_mem_of_subset asu _,
    exact add_comm_group.to_add_comm_monoid M,
    exact _inst_5,exact coe_to_lift,
    simp,
    convert asu,
    simp,
    refine set.mem_of_mem_of_subset _ this,
    simp,
    rintros?,
    dsimp,
-/
     },
  { --rw [mem_coe] at hm,
    rcases mem_span_set.mp hm with ⟨c, csup, rfl⟩,
    rw [mem_carrier, mem_coe],
    refine sum_mem _ _,
    intros a as,
    dsimp,
    rcases ff (c a) with ⟨ca, cap | can⟩,
    rw [cap, algebra_map_smul],
    refine smul_mem _ ca _,
    simp,
    sorry,
    sorry,
  },
end

lemma subset.span_union_neg_self_eq_inf {ι R S : Type*} [linear_ordered_field S]
  [comm_semiring R] [semimodule R M] [module S M] [algebra R S] [is_scalar_tower R S M]
  (ff : ∀ s : S, 0 ≤ s → ∃ n d : R, s = algebra_map R S n / algebra_map R S d)
  {v : ι → M} (bv : is_basis S v) {s : finset M} (hRS : is_inj_nonneg (algebra_map R S)) :
  ∃ sR : finset M, (sR : set M) ⊆ (submodule.span R (set.range v ∪ set.range (λ i, - v i))) ∧
    (submodule.span R (sR : set M)).carrier =
      submodule.span R (set.range v) ∩ submodule.span S (set.range v) :=
begin
  sorry,
end

end pairing

end concrete
