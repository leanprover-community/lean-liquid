import topology.algebra.ordered
import toric.scattered_defs
import toric.is_inj_nonneg
import toric.pointed
import toric.pairing_dual_saturated

/-! In the intended application, these are the players:
* `R = ℕ`;
* `S = ℤ`;
* `M`and `N` are free finitely generated `ℤ`-modules that are dual to each other;
* `P = ℤ` is the target of the natural pairing `M ⊗ N → ℤ`.
-/

--open_locale big_operators classical

variables {R S M : Type*} [comm_semiring R] [add_comm_group M] [semimodule R M]

open pairing submodule

/--
In a compatible tower `R → S → M`, with `S` an `R`-algebra and `M` an `S`-module,
if `S` is finite over `R` and `M` is finitely generated over `S`, then `M` is finite over `R`.
This lemma is essentially already in mathlib, and it is called `span_smul`: in this version,
we keep track of the finiteness hypotheses.
-/
lemma finite.span_restrict [semiring S] [semimodule S M] [algebra R S]
  [is_scalar_tower R S M] {G : set S} {v : set M}
  (fG : G.finite) (spg : submodule.span R G = ⊤)
  (fv : v.finite) (hv : submodule.span S v = ⊤) :
  ∃ t : set M, t.finite ∧ submodule.span R (t : set M) = (span S (v : set M)).restrict_scalars R :=
⟨G • v, fG.image2 (•) fv, span_smul spg v⟩

/--
In a compatible tower `R → S → M`, with `S` an `R`-algebra and `M` an `S`-module,
if `S` is finite over `R` and `M` is finitely generated over `S`, then `M` is finite over `R`.
This lemma is essentially already in mathlib, and it is called `span_smul`: in this version,
we keep track of the finset hypotheses.
-/
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

/-- The choices of coefficients from the set `zq` that give rise to integral elements of `M`
contained in the rational vector subspace spanned by `s`. -/
def generating_box (Z : Type*) {Q ι : Type*} [comm_ring Z] [field Q] [algebra Z Q]
  [semimodule Z M] [semimodule Q M] [is_scalar_tower Z Q M]
  (v : ι → M) (s : set M) (zq : set Q) : set (finsupp ι Q) :=
  { f | ∀ i : ι, (f i = 0 ∨ f i ∈ zq) ∧
    f.sum (λ i q, q • v i) ∈
      submodule.span Z (set.range v) ⊓ (submodule.span Q s).restrict_scalars Z }

lemma gen_box_sum  (Z : Type*) {Q ι : Type*} [comm_ring Z] [field Q] [algebra Z Q]
  [semimodule Z M] [semimodule Q M] [is_scalar_tower Z Q M]
  (v : ι → M) (s : set M) (zq : set Q) {z : M}
  (hz : z ∈ span Z {m : M | ∃ (f : ι →₀ Q), f ∈ generating_box Z v s zq ∧
    m = f.sum (λ (i : ι) (q : Q), q • v i)}) :
  z ∈ submodule.span Z (set.range v) ⊓ (submodule.span Q s).restrict_scalars Z :=
begin
--  tidy?,
  sorry
end

lemma sets {α : Type*} {a b c : set α} (hc : c ⊆ a ∪ b) : c = (c ∩ a) ∪ (c ∩ b) :=
begin
  ext1,
  refine ⟨λ g, _, _⟩,
  { cases (hc g : x ∈ a ∪ b) with h h,
    { exact or.inl ⟨g, h⟩ },
    { exact or.inr ⟨g, h⟩ } },
  { rintro (⟨xc, xa⟩ | ⟨xc, xb⟩);
    assumption }
end

lemma sets_finite_of_subset_finite {α : Type*} {a b : set α} (fa : a.finite) (ba : b ⊆ a) :
  b.finite :=
set.finite.subset fa ba


lemma sets_finite_inter {α : Type*} {a b : set α} (fa : a.finite) : (a ∩ b).finite :=
set.finite.subset fa (set.inter_subset_left a b)


lemma saturated_generation {Z Q ι : Type*} [comm_ring Z] [field Q] [algebra Z Q]
  [semimodule Z M] [semimodule Q M] [is_scalar_tower Z Q M]
  {v : ι → M} (bv : is_basis Q v) (s : set M) (hs : s ⊆ submodule.span Z (set.range v))
  {zq : set Q} (hzq : submodule.span Z zq = ⊤) :
  submodule.span Z (s ∪
    { m : M | ∃ f : finsupp ι Q, (f ∈ generating_box Z v s zq) ∧ m = f.sum (λ i q, q • v i) }) =    submodule.span Z (set.range v) ⊓ (submodule.span Q s).restrict_scalars Z :=
begin
  rw span_union,
  ext a,
  refine ⟨_, _⟩; intros hx,
  {
    rcases mem_sup.mp hx with ⟨y, ys, z, zx, rfl⟩,
--    rw mem_sup at hx,
    unfold generating_box at zx,
    simp at zx,
    refine ⟨_, _⟩,
sorry,sorry,
  },
  sorry,
end

#exit
  classical,
  ext x,
  refine ⟨_, _⟩; intros hx,
  {
    simp only [mem_inf, restrict_scalars_mem],
    refine ⟨_, _⟩,
    work_on_goal 0
    { rcases mem_span_set.mp hx with ⟨c, csup, rfl⟩,
      have : (c.support : set M) = (c.support ∩ s) ∪ (c.support ∩ { m : M | ∃ f : finsupp ι Q,
        (f ∈ generating_box Z v s zq) ∧ m = f.sum (λ i q, q • v i) }) := sets csup,
      haveI csf : (c.support ∩ s : set M).finite := sets_finite_inter c.support.finite_to_set,
      haveI cxf : (c.support ∩
        {m : M | ∃ (f : ι →₀ Q), f ∈ generating_box Z v s zq ∧
          m = f.sum (λ (i : ι) (q : Q), q • v i)} : set M).finite :=
          sets_finite_inter c.support.finite_to_set,
      have : (c.support) = ((c.support : set M) ∩ s).to_finset ∪ ((c.support : set M) ∩ { m : M | ∃ f : finsupp ι Q,
        (f ∈ generating_box Z v s zq) ∧ m = f.sum (λ i q, q • v i) }).to_finset,
      ext a,
  obtain F := set.ext_iff.mp this a,
  simp only [set.mem_inter_eq, finsupp.mem_support_iff, ne.def, set.mem_union_eq, set.mem_set_of_eq, finset.mem_coe] at F,
  simpa only [set.mem_inter_eq, set.mem_to_finset, finsupp.mem_support_iff, finset.mem_union, finset.mem_coe],



      sorry,
      rintros _ ⟨⟨Hc, H0, Hadd, Hsmul⟩, rfl⟩,
      rintros _ ⟨H, rfl⟩,
      dsimp at H,
      injections_and_clear,
      --simp only [mk_coe, set.Inter_eq_univ, set.mem_set_of_eq] at *,
    },
    work_on_goal 1
    { rintros t ⟨⟨Hc, H0, Hadd, Hsmul⟩, rfl⟩,
      rintros _ ⟨H, rfl⟩,
      dsimp at H,
      injections_and_clear,
      --simp only [mk_coe, set.Inter_eq_univ, set.mem_set_of_eq] at *,
    },

  },
  sorry,
end






/- The definition that was left after talking to Johan. -/
def generating_box {Z Q ι : Type*} [comm_ring Z] [field Q] [algebra Z Q]
  [semimodule Z M] [semimodule Q M] [is_scalar_tower Z Q M]
  {v : ι → M} (bv : is_basis Q v) (s : set M) (hs : s ⊆ submodule.span Z (set.range v))
  {zq : set Q} (hzq : submodule.span Z zq = ⊤) : set (finsupp ι Q) :=
  { f | ∀ i : ι, (f i = 0 ∨ f i ∈ zq) ∧
    f.sum (λ i q, q • v i) ∈ submodule.span Z (set.range v) ⊓ (submodule.span Q s).restrict_scalars Z }


lemma saturated_generation {Z Q ι : Type*} [comm_ring Z] [field Q] [algebra Z Q]
  [semimodule Z M] [semimodule Q M] [is_scalar_tower Z Q M]
  {v : ι → M} (bv : is_basis Q v) (s : set M) (hs : s ⊆ submodule.span Z (set.range v))
  {zq : set Q} (hzq : submodule.span Z zq = ⊤) :
  ∃ fs : set Q, submodule.span Z (zq • s) =
    submodule.span Z (set.range v) ⊓ (submodule.span Q s).restrict_scalars Z :=
sorry

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

lemma set.algebra_map_smul {R S M : Type*} [add_comm_monoid M] [comm_semiring R] [semimodule R M] [semiring S]
  [semimodule S M] [algebra R S] [is_scalar_tower R S M]
  (s : set M) (rs : set R) :
  ((algebra_map R S) '' rs • s) = (rs • s) :=
begin
  ext,
  refine ⟨_, _⟩,
  { rintro ⟨_, m, ⟨r, rrs, rfl⟩, ms, rfl⟩,
    exact ⟨_, _, rrs, ms, (algebra_map_smul _ _ _).symm⟩ },
  { rintro ⟨r, m, rrs, ms, rfl⟩,
    refine set.mem_smul.mpr _,
    refine ⟨_, m, set.mem_image_of_mem (algebra_map R S) rrs, ms, algebra_map_smul S r m⟩ }
end


-- could it work with `mul_zero_class R`?
/--  The submodule spanned by a set `s` over an `R`-algebra `S` is spanned as an `R`-module by
`s ∪ - s`, if for every element `a ∈ S`, either `a` or `- a` is in the image of `R`. -/
lemma subset.span_multiples {R : Type*} [integral_domain R] [semimodule R M]
  [field S] [module S M]
  [algebra R S]
  [is_scalar_tower R S M]
  (inj : function.injective (algebra_map R S))
  (ff : ∀ a : S, ∃ n d : R, is_regular d ∧ algebra_map R S d * a = algebra_map R S n) (s : set M)
  (rs : set R) (hrs : ∀ a ∈ rs, is_regular a) (sprs : span R ((algebra_map R S) '' rs) = ⊤) :
  saturation (submodule.span R (s)) = (submodule.span S (s : set M)).restrict_scalars R :=
begin
  ext m,
  refine ⟨_, _⟩; intros hx,
  rw ← span_smul sprs,
  rcases hx with ⟨r, hr, rm⟩,
  rw set.algebra_map_smul,


  refine (restrict_scalars_mem R (span S s) _).mpr _,
  have : algebra_map R S r • m ∈ span S s,
  { simp only [algebra_map_smul],
    rw mem_span_set,
    rcases mem_span_set.mp rm with ⟨c, csup, rid⟩,
    set su : set M := {n : M | n ∈ (c.support : set M) ∧ algebra_map R S (c n) ≠ 0},
    have : su.finite := set.finite.subset c.support.finite_to_set (λ _ hs, hs.1),
    let l : M →₀ S := begin
    { refine ⟨this.to_finset, algebra_map R S ∘ c, λ a, _⟩,
      refine ⟨λ ha, ((set.finite.mem_to_finset _).mp ha).2, λ k, _⟩,
      refine (set.finite.mem_to_finset _).mpr ⟨finset.mem_coe.mpr _, k⟩,
      refine (finsupp.mem_support_iff.mpr (λ h, k (_ : (algebra_map R S) (c a) = 0))),
      rw h,
      exact (algebra_map R S).map_zero }
    end,
    refine ⟨l, set.subset.trans (λ d hd, _) csup, _⟩,
      rw set.finite.coe_to_finset at hd,
      exact hd.1,
      rw ← rid,
      sorry,
--    simp at ⊢ hd,
     },
  obtain ⟨n, d, rd, rr⟩ := ff ((algebra_map R S) r),
  simp only [algebra_map_smul] at this,


  unfold saturation at hx,

  apply mem_span_set.mpr,

end

-- could it work with `mul_zero_class R`?
/--  The submodule spanned by a set `s` over an `R`-algebra `S` is spanned as an `R`-module by
`s ∪ - s`, if for every element `a ∈ S`, either `a` or `- a` is in the image of `R`. -/
lemma subset.span_multiples {R : Type*} [integral_domain R] [semimodule R M]
  [ordered_comm_ring S] [module S M]
  [algebra R S]
  [is_scalar_tower R S M]
--  [mul_zero_class R]
  (ff : ∀ a : S, ∃ n d : R, is_regular d ∧ algebra_map R S d * a = algebra_map R S n) (s : set M) :
  saturation (submodule.span R (s)) = (submodule.span S (s : set M)).restrict_scalars R :=
begin
  ext m,
  refine ⟨_, _⟩; intros hx,
  refine (restrict_scalars_mem R (span S s) _).mpr _,
  rcases hx with ⟨r, hr, rm⟩,
  have : algebra_map R S r • m ∈ span S s,
  { simp only [algebra_map_smul],
    rw mem_span_set,
    rcases mem_span_set.mp rm with ⟨c, csup, rid⟩,
    set su : set M := {n : M | n ∈ (c.support : set M) ∧ algebra_map R S (c n) ≠ 0},
    have : su.finite := set.finite.subset c.support.finite_to_set (λ _ hs, hs.1),
    let l : M →₀ S := begin
    { refine ⟨this.to_finset, algebra_map R S ∘ c, λ a, _⟩,
      refine ⟨λ ha, ((set.finite.mem_to_finset _).mp ha).2, λ k, _⟩,
      refine (set.finite.mem_to_finset _).mpr ⟨finset.mem_coe.mpr _, k⟩,
      refine (finsupp.mem_support_iff.mpr (λ h, k (_ : (algebra_map R S) (c a) = 0))),
      rw h,
      exact (algebra_map R S).map_zero }
    end,
    refine ⟨l, set.subset.trans (λ d hd, _) csup, _⟩,
      rw set.finite.coe_to_finset at hd,
      exact hd.1,
      rw ← rid,
      sorry,
--    simp at ⊢ hd,
     },
  obtain ⟨n, d, rd, rr⟩ := ff ((algebra_map R S) r),
  simp only [algebra_map_smul] at this,


  unfold saturation at hx,

  apply mem_span_set.mpr,

end


-- this may not be what I want, if I understand correctly restrict_scalars.
/--  The submodule spanned by a set `s` over an `R`-algebra `S` is spanned as an `R`-module by
`s ∪ - s`, if for every element `a ∈ S`, either `a` or `- a` is in the image of `R`. -/
lemma subset.span_multiples [ordered_comm_ring S] [module S M] [algebra R S]
  [is_scalar_tower R S M]
  (ff : ∀ a : S, ∃ n d : R, is_regular d ∧ algebra_map R S d * a = algebra_map R S n) (s : set M) :
  (submodule.span R ((⊤ : set R) • s)) = (submodule.span S (s : set M)).restrict_scalars R :=
begin

end



/-
Below are lemmas with incomplete proofs that may not be needed, but I am not yet ready to let go.
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
-/
