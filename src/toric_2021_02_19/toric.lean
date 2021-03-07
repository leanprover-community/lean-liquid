import topology.algebra.ordered
import toric_2021_02_19.scattered_defs
import toric_2021_02_19.is_inj_nonneg
import toric_2021_02_19.PR_made
import toric_2021_02_19.pointed
import toric_2021_02_19.pairing_dual_saturated

/-! In the intended application, these are the players:
* `R = ℕ`;
* `S = ℤ`;
* `M`and `N` are free finitely generated `ℤ`-modules that are dual to each other;
* `P = ℤ` is the target of the natural pairing `M ⊗ N → ℤ`.
-/

open_locale big_operators classical

variables {R S M : Type*} [comm_semiring R] [add_comm_group M] [semimodule R M]

namespace pairing

open pairing submodule

lemma finite.span_restrict [semiring S] [semimodule S M] [algebra R S]
  [is_scalar_tower R S M] {G : set S} {v : set M}
  (fG : G.finite) (spg : submodule.span R G = ⊤)
  (fv : v.finite) (hv : submodule.span S v = ⊤) :
  ∃ t : set M, t.finite ∧ submodule.span R (t : set M) = (span S (v : set M)).restrict_scalars R :=
⟨G • v, fG.image2 (•) fv, span_smul spg v⟩

lemma finset.span_restrict [semiring S] [semimodule S M] [algebra R S]
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
lemma subset.span_union_neg_self_eq [ordered_comm_ring S] [module S M] [algebra R S]
  [is_scalar_tower R S M]
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


/--  The submodule spanned by a set `s` over an `R`-algebra `S` is spanned as an `R`-module by
`s ∪ - s`, if for every element `a ∈ S`, either `a` or `- a` is in the image of `R`. -/
lemma finset.restrict_inf_span [ordered_semiring S] [topological_space S]
  [order_topology S] [semimodule S M] [algebra R S] [is_scalar_tower R S M]
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


lemma finset.span_union_neg_self_eq {ι : Type*} [ordered_comm_ring S]
  [module S M] [algebra R S] [is_scalar_tower R S M]
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

lemma subset.span_union_neg_self_eq_inf {ι : Type*} [linear_ordered_field S]
  [module S M] [algebra R S] [is_scalar_tower R S M]
  (ff : ∀ s : S, 0 ≤ s → ∃ n d : R, s = algebra_map R S n / algebra_map R S d)
  {v : ι → M} (bv : is_basis S v) {s : finset M} (hRS : is_inj_nonneg (algebra_map R S)) :
  ∃ sR : finset M, (sR : set M) ⊆ (submodule.span R (set.range v ∪ set.range (λ i, - v i))) ∧
    (submodule.span R (sR : set M)).carrier =
      submodule.span R (set.range v) ∩ submodule.span S (set.range v) :=
begin
  sorry,
end

end pairing
