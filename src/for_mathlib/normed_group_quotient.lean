import for_mathlib.normed_group_hom

variables {V V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group V₁] [normed_group V₂] [normed_group V₃]
variables (f g : normed_group_hom V₁ V₂)

namespace normed_group_hom -- probably needs to change
section quotient

open quotient_add_group

variables {M N : Type*} [normed_group M] [normed_group N]

/-- The definition of the norm on the quotient by an additive subgroup. -/
noncomputable
instance norm_on_quotient (S : add_subgroup M) : has_norm (quotient S) :=
{ norm := λ x, Inf {r : ℝ | ∃ (y : M), quotient_add_group.mk' S y = x ∧ r = ∥y∥ } }

/-- The norm of the image under the natural morphism to the quotient. -/
lemma quotient_norm_eq (S : add_subgroup M) (m : M) :
  ∥quotient_add_group.mk' S m∥ = Inf {r : ℝ | ∃ s ∈ S, r = ∥m + s∥ } :=
begin
  suffices : {r | ∃ (y : M), quotient_add_group.mk' S y = (quotient_add_group.mk' S m) ∧ r = ∥y∥ } =
    {r : ℝ | ∃ s ∈ S, r = ∥m + s∥ },
  { simp only [this, norm] },
  ext r,
  split,
  { intro h,
    obtain ⟨n, hn, rfl⟩ := h,
    use n - m,
    split,
    { rw [← quotient_add_group.ker_mk S, add_monoid_hom.mem_ker, add_monoid_hom.map_sub, hn,
        sub_self] },
    { rw add_sub_cancel'_right } },
  { intro h,
    obtain ⟨s, hs, rfl⟩ := h,
    use m + s,
    refine ⟨_, rfl⟩,
    have hker : s ∈ (quotient_add_group.mk' S).ker := by rwa [quotient_add_group.ker_mk S],
    rw [add_monoid_hom.mem_ker] at hker,
    rw [add_monoid_hom.map_add, hker, add_zero] }
end

/-- The norm of the projection is smaller or equal to the norm of the original element. -/
lemma norm_mk_le (S : add_subgroup M) (m : M) : ∥quotient_add_group.mk' S m∥ ≤ ∥m∥ :=
begin
  unfold norm,
  refine real.Inf_le _ (⟨0, λ r hr, _⟩) _,
  { rw [set.mem_set_of_eq] at hr,
    obtain ⟨m, hm, rfl⟩ := hr,
    exact norm_nonneg m },
  { rw [set.mem_set_of_eq],
    exact ⟨m, rfl, rfl⟩ }
end

/-- The quotient norm is nonnegative. -/
lemma norm_mk_nonneg (S : add_subgroup M) (m : M) : 0 ≤ ∥quotient_add_group.mk' S m∥ :=
begin
  refine real.lb_le_Inf _ _ _,
  { use ∥m∥,
    rw [set.mem_set_of_eq],
    exact ⟨m, rfl, rfl⟩ },
  intros y hy,
  rw [set.mem_set_of_eq] at hy,
  obtain ⟨z, hz, rfl⟩ := hy,
  exact norm_nonneg z
end

lemma norm_mk_lt {S : add_subgroup M} (x : (quotient S)) {ε : ℝ} (hε : 0 < ε) :
  ∃ (m : M), quotient_add_group.mk' S m = x ∧ ∥m∥ < ∥x∥ + ε :=
begin
  obtain ⟨r, hr, hnorm⟩ := (real.Inf_lt _ _ _).1 (lt_add_of_pos_right (∥x∥) hε),
  { simp only [set.mem_set_of_eq] at hr,
    obtain ⟨m₁, hm₁⟩ := hr,
    exact ⟨m₁, hm₁.1, by rwa [← hm₁.2]⟩ },
  { obtain ⟨m, hm⟩ := quot.exists_rep x,
    use ∥m∥,
    rw [set.mem_set_of_eq],
    exact ⟨m, hm, rfl⟩ },
  { refine ⟨0, λ r h, _⟩,
    rw [set.mem_set_of_eq] at h,
    obtain ⟨z, hz, rfl⟩ := h,
    exact norm_nonneg z }
end

lemma norm_mk_lt' (S : add_subgroup M) (m : M) {ε : ℝ} (hε : 0 < ε) :
  ∃ s ∈ S, ∥m + s∥ < ∥quotient_add_group.mk' S m∥ + ε :=
begin
  obtain ⟨n, hn⟩ := norm_mk_lt (quotient_add_group.mk' S m) hε,
  use n - m,
  split,
  { rw [← quotient_add_group.ker_mk S, add_monoid_hom.mem_ker, add_monoid_hom.map_sub, hn.1,
    sub_self] },
  { simp only [add_sub_cancel'_right],
    exact hn.2 }
end

/-- The quotient norm of `0` is `0`. -/
lemma norm_mk_zero (S : add_subgroup M) : ∥(0 : (quotient S))∥ = 0 :=
begin
  refine le_antisymm _ (norm_mk_nonneg S 0),
  simpa [norm_zero, add_monoid_hom.map_zero] using norm_mk_le S 0
end

/-- If `(m : M)` has norm equal to `0` in `quotient S` for a complete subgroup `S` of `M`, then
`m ∈ S`. -/
lemma norm_zero_eq_zero (S : add_subgroup M) [complete_space S] (m : M)
  (h : ∥(quotient_add_group.mk' S) m∥ = 0) : m ∈ S :=
begin
  choose g hg using λ n, (norm_mk_lt' S m (@nat.one_div_pos_of_nat ℝ _ n)),
  simp only [h, one_div, zero_add] at hg,
  have hcauchy : cauchy_seq g,
  { rw metric.cauchy_seq_iff,
    intros ε hε,
    obtain ⟨k, hk⟩ := exists_nat_ge (ε/2)⁻¹,
    have kpos := lt_of_lt_of_le (inv_pos.mpr (half_pos hε)) hk,
    replace hk := (inv_le_inv kpos (inv_pos.mpr (half_pos hε))).2 hk,
    rw [inv_inv'] at hk,
    refine ⟨k, λ a b ha hb, _⟩,
    have apos := lt_trans (lt_of_lt_of_le kpos (nat.cast_le.2 (ge.le ha))) (lt_add_one a),
    have bpos := lt_trans (lt_of_lt_of_le kpos (nat.cast_le.2 (ge.le hb))) (lt_add_one b),
    replace ha : (k : ℝ ) ≤ ↑(a + 1) := nat.cast_le.2 (le_add_right ha),
    replace hb : (k : ℝ ) ≤ ↑(b + 1) := nat.cast_le.2 (le_add_right hb),
    have haε := le_trans ((inv_le_inv apos kpos).2 ha) hk,
    have hbε := le_trans ((inv_le_inv bpos kpos).2 hb) hk,
    calc dist (g a) (g b)
        = ∥(g a) - (g b)∥ : dist_eq_norm _ _
    ... = ∥(m + (g a)) + (-(m + (g b)))∥ : by abel
    ... ≤ ∥m + (g a)∥ + ∥-(m + (g b))∥ : norm_add_le _ _
    ... = ∥m + (g a)∥ + ∥m + (g b)∥ : by rw [norm_neg _]
    ... < (↑a + 1)⁻¹ + (↑b + 1)⁻¹ : add_lt_add (hg a).2 (hg b).2
    ... ≤ ε/2 + ε/2 : add_le_add haε hbε
    ... = ε : add_halves ε },
  have Scom : is_complete (S : set M) :=
    complete_space_coe_iff_is_complete.mp (by assumption),
  suffices : m ∈ (S : set M), by exact this,
  obtain ⟨s, hs, hlim⟩ := cauchy_seq_tendsto_of_is_complete Scom (λ n, (hg n).1) hcauchy,
  suffices : ∥m + s∥ = 0,
  { rw [norm_eq_zero] at this,
    rw [eq_neg_of_add_eq_zero this],
    exact add_subgroup.neg_mem S hs },
  have hlimnorm : filter.tendsto (λ n, ∥m + (g n)∥) filter.at_top (nhds 0),
  { apply (@metric.tendsto_at_top _ _ _ ⟨0⟩ _ _ _).2,
    intros ε hε,
    obtain ⟨k, hk⟩ := exists_nat_ge ε⁻¹,
    have kpos := lt_of_lt_of_le (inv_pos.mpr hε) hk,
    replace hk := (inv_le_inv kpos (inv_pos.mpr hε)).2 hk,
    rw [inv_inv'] at hk,
    refine ⟨k, λ n hn, _⟩,
    replace hn : (k : ℝ) ≤ ↑(n + 1) := nat.cast_le.2 (le_add_right hn),
    have npos : (0 : ℝ) < ↑(n + 1) := nat.cast_lt.2 (nat.succ_pos n),
    replace hn := le_trans ((inv_le_inv npos kpos).2 hn) hk,
    simp only [dist_zero_right, norm_norm],
    calc ∥m + g n∥
        < (↑n + 1)⁻¹ : (hg n).2
    ... ≤ ε : hn },
  exact tendsto_nhds_unique ((continuous.to_sequentially_continuous (@continuous_norm M _))
    (λ (n : ℕ), m + g n) (tendsto.const_add m hlim)) hlimnorm
end

/-- The norm on `quotient S` is actually a norm if `S` is a complete subgroup of `M`. -/
lemma quotient.is_normed_group.core (S : add_subgroup M) [complete_space S] :
  normed_group.core (quotient S) :=
begin
  split,
  { intro x,
    refine ⟨λ h, _ , λ h, by simpa [h] using norm_mk_zero S⟩,
    obtain ⟨m, hm⟩ := surjective_quot_mk _ x,
    replace hm : quotient_add_group.mk' S m = x := hm,
    rw [← hm, ← add_monoid_hom.mem_ker, quotient_add_group.ker_mk],
    rw [← hm] at h,
    exact norm_zero_eq_zero S m h },
  { intros x y,
    refine le_of_forall_pos_le_add (λ ε hε, _),
    replace hε := half_pos hε,
    obtain ⟨m, hm⟩ := norm_mk_lt x hε,
    obtain ⟨n, hn⟩ := norm_mk_lt y hε,
    have H : quotient_add_group.mk' S (m + n) = x + y := by rw [add_monoid_hom.map_add, hm.1, hn.1],
    calc  ∥x + y∥
        = ∥quotient_add_group.mk' S (m + n)∥ : by rw [← H]
    ... ≤ ∥m + n∥ : norm_mk_le _ _
    ... ≤ ∥m∥ + ∥n∥ : norm_add_le _ _
    ... ≤ (∥x∥ + ε/2) + (∥y∥ + ε/2) : add_le_add (le_of_lt hm.2) (le_of_lt hn.2)
    ... = ∥x∥ + ∥y∥ + ε : by ring },
  { intro x,
    suffices : {r : ℝ | ∃ (y : M), quotient_add_group.mk' S y = x ∧ r = ∥y∥ } =
      {r : ℝ | ∃ (y : M), quotient_add_group.mk' S y = -x ∧ r = ∥y∥ },
    { simp only [this, norm] },
    ext r,
    split,
    { intro h,
      simp only [set.mem_set_of_eq] at h ⊢,
      obtain ⟨m, hm, rfl⟩ := h,
      exact ⟨-m, by simp only [hm, add_monoid_hom.map_neg], by simp only [norm_neg]⟩ },
    { intro h,
      simp only [set.mem_set_of_eq] at h ⊢,
      obtain ⟨m, hm, rfl⟩ := h,
      exact ⟨-m, by simp only [hm, add_monoid_hom.map_neg, eq_self_iff_true, and_self, neg_neg,
        norm_neg]⟩ } }
end

/-- An instance of `normed_group` on the quotient by a subgroup. -/
noncomputable
instance quotient_normed_group (S : add_subgroup M) [complete_space S] :
  normed_group (quotient S) :=
normed_group.of_core (quotient S) (quotient.is_normed_group.core S)

/-- The canonical morphism `M → (quotient S)` as morphism of normed groups. -/
noncomputable
def normed_group.mk (S : add_subgroup M) [complete_space S] : normed_group_hom M (quotient S) :=
{ bound' := ⟨1, λ m, by simpa [one_mul] using norm_mk_le _ m⟩,
  ..quotient_add_group.mk' S }

/-- `normed_group.mk S` agrees with `quotient_add_group.mk' S`. -/
lemma normed_group.mk.apply (S : add_subgroup M) [complete_space S] (m : M) :
  normed_group.mk S m = quotient_add_group.mk' S m := rfl

/-- `normed_group.mk S` is surjective. -/
lemma surjective_normed_group.mk (S : add_subgroup M) [complete_space S] :
  function.surjective (normed_group.mk S) :=
surjective_quot_mk _

/-- The kernel of `normed_group.mk S` is `S`. -/
lemma normed_group.mk.ker (S : add_subgroup M) [complete_space S] : (normed_group.mk S).ker = S :=
quotient_add_group.ker_mk  _

/-- `is_quotient f`, for `f : M ⟶ N` means that `N` is isomorphic to the quotient of `M`
by the kernel of `f`. -/
structure is_quotient (f : normed_group_hom M N) : Prop :=
(surjective : function.surjective f)
(norm : ∀ x, ∥f x∥ = Inf {r : ℝ | ∃ y ∈ f.ker, r = ∥x + y∥ })

/-- `normed_group.mk S` satisfies `is_quotient`. -/
lemma is_quotient_quotient (S : add_subgroup M) [complete_space S] :
  is_quotient (normed_group.mk S) :=
⟨surjective_normed_group.mk S, λ m, by simpa [normed_group.mk.ker S] using quotient_norm_eq S m⟩

lemma quotient_norm_lift {f : normed_group_hom M N} (hquot : is_quotient f) {ε : ℝ} (hε : 0 < ε)
  (n : N) : ∃ (m : M), f m = n ∧ ∥m∥ < ∥n∥ + ε :=
begin
  have hlt := lt_add_of_pos_right (∥n∥) hε,
  obtain ⟨m, hm⟩ := hquot.surjective n,
  nth_rewrite 0 [← hm] at hlt,
  rw [hquot.norm m] at hlt,
  replace hlt := (real.Inf_lt _ _ _).1 hlt,
  { obtain ⟨r, hr, hlt⟩ := hlt,
    simp only [exists_prop, set.mem_set_of_eq] at hr,
    obtain ⟨m₁, hm₁⟩ := hr,
    use (m + m₁),
    split,
    { rw [normed_group_hom.map_add, (normed_group_hom.mem_ker f m₁).1 hm₁.1, add_zero, hm] },
    rwa [← hm₁.2] },
  { use ∥m∥,
    simp only [exists_prop, set.mem_set_of_eq],
    use 0,
    split,
    { exact (normed_group_hom.ker f).zero_mem },
    { rw add_zero } },
  { use 0,
    intros x hx,
    simp only [exists_prop, set.mem_set_of_eq] at hx,
    obtain ⟨y, hy⟩ := hx,
    rw hy.2,
    exact norm_nonneg _ }
end

lemma quotient_norm_le {f : normed_group_hom M N} (hquot : is_quotient f) (m : M) : ∥f m∥ ≤ ∥m∥ :=
begin
  rw hquot.norm,
  apply real.Inf_le,
  { use 0,
    rintros y ⟨r,hr,rfl⟩,
    simp },
  { refine ⟨0, add_subgroup.zero_mem _, by simp⟩ }
end

end quotient

end normed_group_hom
