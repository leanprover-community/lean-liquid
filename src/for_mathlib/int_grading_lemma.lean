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
subring_of_add_submonoid R Gᵢ
{ carrier := {n : ℤ | 0 ≤ n},
  zero_mem' := le_refl (0 : ℤ),
  add_mem' := @add_nonneg ℤ _ }

universe u
-- doesn't seem to fire (perhaps there was a universe issue which I've since fixed)
instance (R : Type u) [comm_ring R] (Gᵢ : ℤ → add_subgroup R)
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

-- I should comment this
lemma exist_fg_gens {R : Type*} [ring R] {M : Type*} [add_comm_group M] [module R M]
  {S : set M} (hS : (submodule.span R S).fg) :
  ∃ T : finset M, (T : set M) ⊆ S ∧ submodule.span R (T : set M)= submodule.span R S :=
begin
  rcases hS with ⟨U, hU⟩,
  have hU2 : ∀ u ∈ U, ∃ V : finset M, (V : set M) ⊆ S ∧ u ∈ submodule.span R (V : set M),
  { intros,
    apply submodule.mem_span_finite_of_mem_span,
    rw ←hU,
    apply submodule.subset_span,
    exact finset.mem_coe.mpr H },
  choose F hF1 hF2 using hU2,
  classical,
  let T := finset.bUnion U (λ u, if h : u ∈ U then F u h else ∅),
  have hTS : (T : set M) ⊆ S,
  { intros x hx,
    rw finset.mem_coe at hx,
    rw finset.mem_bUnion at hx,
    rcases hx with ⟨a, haU, ha⟩,
    rw dif_pos haU at ha,
    rw ← finset.mem_coe at ha,
    apply hF1 _ haU ha },
  refine ⟨T, hTS, _⟩,
  apply le_antisymm,
  { exact submodule.span_mono hTS },
  { rw [← hU, submodule.span_le],
    intros u hu,
    rw finset.mem_coe at hu,
    specialize hF2 u hu,
    refine submodule.span_mono _ hF2,
    rw finset.coe_subset,
    convert finset.subset_bUnion_of_mem _ hu,
    rw dif_pos hu },
end

lemma aux (R : Type*) (ι : Type*) (G : ι → set R) (T : finset R)
  (p : ι → Prop) (hT : (T : set R) ⊆ ⋃ (i : ι) (H : p i), G i) :
  ∃ F : finset ι, (∀ i ∈ F, p i) ∧ (T : set R) ⊆ ⋃ (i ∈ F), G i :=
begin
  classical,
  revert hT,
  apply finset.induction_on T,
  { intros, exact ⟨∅, by simp⟩ },
  { rintros a s - hS has,
    rcases hS (set.subset.trans (finset.subset_insert a s) has) with ⟨N, hN1, hN2⟩,
    have haS : a ∈ ⋃ (i : ι) (H : p i), G i := has (finset.mem_insert_self _ _),
    rw set.mem_bUnion_iff' at haS,
    rcases haS with ⟨M, hM, haM⟩,
    use insert M N,
    split,
    { intros x hx,
      replace hx := finset.mem_insert.1 hx,
      rcases hx with (rfl | hxs),
      { exact hM },
      { exact hN1 _ hxs } },
    { intros x hx,
      replace hx := finset.mem_insert.1 hx,
      rw set.mem_bUnion_iff',
      rcases hx with (rfl | hxs),
      { exact ⟨M, finset.mem_insert_self M N, haM⟩ },
      { have hxs' : x ∈ (s : set R) := finset.mem_coe.mpr hxs,
        rcases (set.mem_bUnion_iff'.1 (hN2 hxs')) with ⟨i, hi, hi2⟩,
        refine ⟨i, finset.mem_insert_of_mem hi, hi2⟩ } } },
end

open_locale direct_sum

    -- parsing issue on next line *and* why do i have to even let Lean know the type?
    -- let ZZZ := (to_add_monoid (λ (i : ℤ), (Gᵢ i).subtype) : (⨁ i, Gᵢ i) →+ R),


theorem nonnegative_subalgebra_fg_over_zero_subalgebra_of_int_grading_of_noeth
  (R : Type u) [comm_ring R] [is_noetherian_ring R] (Gᵢ : ℤ → add_subgroup R)
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
  have hN : ∃ N : ℤ, (T : set R) ⊆ ⋃ n ∈ set.Ioc 0 N, (Gᵢ n : set R),
  { rcases aux R ℤ (λ i, Gᵢ i) T (λ z, 0 < z) hTS with ⟨F, hF1, hF2⟩,
    by_cases hnon : F.nonempty,
    { use finset.max' F hnon,
      refine set.subset.trans hF2 _,
      intros x hx,
      replace hx := set.mem_bUnion_iff.1 hx,
      rcases hx with ⟨z, hno, hun⟩,
      rw set.mem_bUnion_iff,
      refine ⟨z, _, hun⟩,
      rw set.mem_Ioc,
      refine ⟨hF1 _ hno, F.le_max' _ hno⟩ },
    { use 37,
      refine set.subset.trans hF2 _,
      intros x hx,
      replace hx := set.mem_bUnion_iff.1 hx,
      rcases hx with ⟨z, hno, -⟩,
      exfalso, apply hnon,
      exact ⟨z, hno⟩ } },
  cases hN with N hN,
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
  -- Tnonneg is the finite subset of R_{≥0} which generates I
  letI : decidable_pred (nonneg_piece_subring_of_int_grading Gᵢ : set R) := classical.dec_pred _,
  let Tnonneg := finset.subtype (nonneg_piece_subring_of_int_grading Gᵢ : set R) T,
  letI : decidable_eq R := classical.dec_eq _,
  let gens : ℤ → finset (nonneg_piece_subring_of_int_grading Gᵢ) := λ z,
    finset.subtype (nonneg_piece_subring_of_int_grading Gᵢ : set R) (finset.image (Gᵢ z).subtype (fgset z)),
  -- want finset ↥(nonneg_piece_subring_of_int_grading Gᵢ)
  let Stemp : set ℤ := {z | 1 ≤ z ∧ z ≤ N},
    have hStemp : Stemp.finite := sorry,
  let Stemp2 : finset ℤ := hStemp.to_finset,
  -- nonneggens is the finite subset of R_{≥0} which we claim generates it as an R₀-algebra
  let nonneggens : finset ↥(nonneg_piece_subring_of_int_grading Gᵢ) :=
    Tnonneg ∪ (finset.bUnion Stemp2 gens),
  use nonneggens,
  let R0Tgens := algebra.adjoin ↥(zero_component_subring R Gᵢ)
    (nonneggens : set ↥(nonneg_piece_subring_of_int_grading Gᵢ)),
  change R0Tgens = ⊤,
  suffices : ∀ z, 0 ≤ z → (Gᵢ z).comap
    (nonneg_piece_subring_of_int_grading Gᵢ).subtype.to_add_monoid_hom
    ≤ R0Tgens.to_subring.to_add_subgroup,
  { ext x, simp only [iff_true, algebra.mem_top],
    cases x with x hx,
    have foo := (sum_decomposition Gᵢ x).symm,
    -- parsing issue on next line *and* why do i have to even let Lean know the type?
    -- let ZZZ := (to_add_monoid (λ (i : ℤ), (Gᵢ i).subtype) : (⨁ i, Gᵢ i) →+ R),
    set x' := (to_add_monoid (λ (i : ℤ), (Gᵢ i).subtype) : (⨁ i, Gᵢ i) →+ R)
      ((add_subgroup_decomposition Gᵢ) x) with x'def,
    have hx' : x' ∈ nonneg_piece_subring_of_int_grading Gᵢ,
    { rwa foo at hx },
    suffices : (⟨x', hx'⟩ : nonneg_piece_subring_of_int_grading Gᵢ) ∈ R0Tgens,
    { convert this },
    sorry },
  sorry,
end

end has_add_subgroup_decomposition

end direct_sum
