import for_mathlib.grading_zero_subring

/-

## A technical lemma about Noetherian ℤ-graded rings

We need the following theorem for Gordan's Lemma:

If A is ℤ-graded and Noetherian then A_{≥0} is a finitely-generated A₀-algebra

-/

namespace direct_sum

namespace has_add_subgroup_decomposition

def nonneg_piece_subring_of_int_grading {R : Type*} [ring R] (Gᵢ : ℤ → add_subgroup R)
  [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ] : subring R :=
subring_of_add_subgroup R Gᵢ
{ carrier := {n : ℤ | 0 ≤ n},
  zero_mem' := le_refl (0 : ℤ),
  add_mem' := @add_nonneg ℤ _ }

-- doesn't seem to fire
instance (R : Type*) [comm_ring R] (Gᵢ : ℤ → add_subgroup R)
  [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ] :
  algebra (zero_component_subring R Gᵢ) (nonneg_piece_subring_of_int_grading Gᵢ) :=
ring_hom.to_algebra $ subring.incl R
  (zero_component_subring R Gᵢ) (nonneg_piece_subring_of_int_grading Gᵢ)
begin
  intros r hr n hn,
  change r ∈ Gᵢ 0 at hr,
  change ¬0 ≤ n at hn,
  rw mem_piece_iff_single_support at hr,
  apply hr,
  apply ne_of_lt,
  exact not_le.mp hn,
end


lemma exist_fg_gens {R : Type*} [ring R] {M : Type*} [add_comm_group M] [module R M]
  {S : set M} (hS : (submodule.span R S).fg) :
  ∃ T : finset M, (T : set M) ⊆ S ∧ submodule.span R (T : set M)= submodule.span R S :=
begin
  sorry
end

theorem nonnegative_subalgebra_fg_over_zero_subalgebra_of_int_grading_of_noeth
  (R : Type*) [comm_ring R] [is_noetherian_ring R] (Gᵢ : ℤ → add_subgroup R)
  [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ] :
@algebra.finite_type (zero_component_subring R Gᵢ) (nonneg_piece_subring_of_int_grading Gᵢ) _ _
(direct_sum.has_add_subgroup_decomposition.nonneg_piece_subring_of_int_grading.algebra R Gᵢ)
:=
begin
  -- see pdf for proof details
  haveI h : ∀ a : ℤ, is_noetherian (Gᵢ 0) (Gᵢ a) :=
    component_submodule.component_submodule_noetherian Gᵢ,
  let S := ⋃ (n > 0), (Gᵢ n : set R),
  let I : submodule R R := submodule.span R S,
  have hI : I.fg := is_noetherian.noetherian I,
  rcases exist_fg_gens hI with ⟨T, hTS, (heq : submodule.span R (T : set R) = I)⟩,
  -- T is finite so it contained in `⋃_{0<n≤N} R_n` for some large `N`
  -- this could be abstracted out
  have HN : ∃ N : ℤ, (T : set R) ⊆ ⋃ n ∈ set.Ioc 0 N, (Gᵢ n : set R),
  { -- proof by induction on size of T
    classical, revert hTS, apply finset.induction_on T,
    { intros, exact ⟨37, by simp⟩ },
    { rintros a s - hS has,
      cases hS (set.subset.trans (finset.subset_insert a s) has) with N hN,
      have haS : a ∈ S := has (finset.mem_insert_self _ _),
      replace haS := set.mem_bUnion_iff.1 haS, -- why rw no work?
      rcases haS with ⟨M, (hM : 1 ≤ M), haM⟩,
      use max M N,
      intros x hx,
      replace hx := finset.mem_insert.1 hx,
      rcases hx with (rfl | hxs),
      { rw set.mem_bUnion_iff,
        use M,
        refine ⟨_, haM⟩,
        -- obviously
        simp, split, linarith, left, refl },
      { specialize hN hxs,
        rw set.mem_bUnion_iff at ⊢ hN,
        rcases hN with ⟨A, hA, h⟩,
        refine ⟨A, _, h⟩,
        rw [set.mem_Ioc] at ⊢ hA,
        cases hA with hA1 hA2,
        exact ⟨hA1, hA2.trans (le_max_right _ _)⟩ } } },
  -- generating set is T union generators of Gᵢ n for 0≤n≤N
  -- will need finset.bUnion (union of finsets over a finset)
  choose fgset fgpf using λ z, is_noetherian.noetherian (⊤ : submodule (Gᵢ 0) (Gᵢ z)),
  have nonneg_in : ∀ z : ℤ, 0 ≤ z → (Gᵢ z : set R) ⊆ nonneg_piece_subring_of_int_grading Gᵢ,
  { rintros z hz x (hxz : x ∈ Gᵢ z) a (ha : ¬ (0 ≤ a)),
    rw mem_piece_iff_single_support at hxz,
    apply hxz,
    rintro rfl,
    exact ha hz },
  have S_in_nonneg : S ⊆ nonneg_piece_subring_of_int_grading Gᵢ,
  { intros s hsS,
    replace hsS := set.mem_bUnion_iff.1 hsS,
    rcases hsS with ⟨z, (hz : 1 ≤ z), hsz⟩,
    exact nonneg_in z (zero_le_one.trans hz) hsz },
  -- want finset ↥(nonneg_piece_subring_of_int_grading Gᵢ)
  sorry
end

-- note : we now have `add_monoid_algebra.finite_type_iff_fg`

end has_add_subgroup_decomposition

end direct_sum
