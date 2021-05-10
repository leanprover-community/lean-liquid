import analysis.normed_space.normed_group_hom

noncomputable theory


open quotient_add_group metric set
open_locale topological_space nnreal

variables {M N : Type*} [semi_normed_group M] [semi_normed_group N]
variables {M₁ N₁ : Type*} [normed_group M₁] [normed_group N₁]

@[simp]
lemma mem_ball_0_iff {ε : ℝ} {x : M} : x ∈ ball (0 : M) ε ↔ ∥x∥ < ε :=
by rw [mem_ball, dist_zero_right]


/-- The definition of the norm on the quotient by an additive subgroup. -/
noncomputable
instance norm_on_quotient (S : add_subgroup M) : has_norm (quotient S) :=
{ norm := λ x, Inf (norm '' {m | mk' S m = x}) }

lemma image_norm_nonempty {S : add_subgroup M} :
  ∀ x : quotient S, (norm '' {m | mk' S m = x}).nonempty :=
begin
  rintro ⟨m⟩,
  rw set.nonempty_image_iff,
  use m,
  change mk' S m = _,
  refl
end

lemma bdd_below_image_norm (s : set M) : bdd_below (norm '' s) :=
begin
  use 0,
  rintro _ ⟨x, hx, rfl⟩,
  apply norm_nonneg
end

lemma quotient_norm_neg {S : add_subgroup M} (x : quotient S) : ∥-x∥ = ∥x∥ :=
begin
  suffices : norm '' {m | mk' S m = x} = norm '' {m | mk' S m = -x},
    by simp only [this, norm],
  ext r,
  split,
  { rintros ⟨m, hm : mk' S m = x, rfl⟩,
    subst hm,
    rw ← norm_neg,
    exact ⟨-m, by simp only [(mk' S).map_neg, set.mem_set_of_eq], rfl⟩ },
  { rintros ⟨m, hm : mk' S m = -x, rfl⟩,
    use -m,
    simp [hm] }
end

lemma quotient_norm_sub_rev {S : add_subgroup M} (x y: quotient S) : ∥x - y∥ = ∥y - x∥ :=
by rw [show x - y = -(y - x), by abel, quotient_norm_neg]
/-- The norm of the projection is smaller or equal to the norm of the original element. -/
lemma quotient_norm_mk_le (S : add_subgroup M) (m : M) :
  ∥mk' S m∥ ≤ ∥m∥ :=
begin
  apply real.Inf_le,
  use 0,
  { rintros _ ⟨n, h, rfl⟩,
    apply norm_nonneg },
  { apply set.mem_image_of_mem,
    rw set.mem_set_of_eq }
end

/-- The norm of the image under the natural morphism to the quotient. -/
lemma quotient_norm_mk_eq (S : add_subgroup M) (m : M) :
  ∥mk' S m∥ = Inf ((λ x, ∥m + x∥) '' S) :=
begin
  change Inf _ = _,
  congr' 1,
  ext r,
  simp_rw [coe_mk', quotient_add_group.eq_iff_sub_mem],
  split,
  { rintros ⟨y, h, rfl⟩,
    use [y - m, h],
    simp },
  { rintros ⟨y, h, rfl⟩,
    use m + y,
    simpa using h },
end

lemma quotient_norm_nonneg (S : add_subgroup M) : ∀ x : quotient S, 0 ≤ ∥x∥ :=
begin
  rintros ⟨m⟩,
  change 0 ≤ ∥mk' S m∥,
  apply real.lb_le_Inf _ (image_norm_nonempty _),
  rintros _ ⟨n, h, rfl⟩,
  apply norm_nonneg
end

/-- The quotient norm is nonnegative. -/
lemma norm_mk_nonneg (S : add_subgroup M) (m : M) : 0 ≤ ∥mk' S m∥ :=
quotient_norm_nonneg S _

lemma quotient_norm_eq_zero_iff (S : add_subgroup M) (m : M) :
  ∥mk' S m∥ = 0 ↔ m ∈ closure (S : set M) :=
begin
  have : 0 ≤ ∥mk' S m∥ := norm_mk_nonneg S m,
  rw [← this.le_iff_eq, quotient_norm_mk_eq, real.Inf_le_iff],
  simp_rw [zero_add],
  { calc (∀ ε > (0 : ℝ), ∃ r ∈ (λ x, ∥m + x∥) '' (S : set M), r < ε) ↔
        (∀ ε > 0, (∃ x ∈ S, ∥m + x∥ < ε)) : by simp [set.bex_image_iff]
     ... ↔ ∀ ε > 0, (∃ x ∈ S, ∥m + -x∥ < ε) : _
     ... ↔ ∀ ε > 0, (∃ x ∈ S, x ∈ metric.ball m ε) : by simp [dist_eq_norm, ← sub_eq_add_neg, norm_sub_rev]
     ... ↔ m ∈ closure ↑S : by simp [metric.mem_closure_iff, dist_comm],
    apply forall_congr, intro ε, apply forall_congr, intro  ε_pos,
    rw [← S.exists_neg_mem_iff_exists_mem],
    simp },
  { use 0,
    rintro _ ⟨x, x_in, rfl⟩,
    apply norm_nonneg },
  rw set.nonempty_image_iff,
  use [0, S.zero_mem]
end

lemma norm_mk_lt {S : add_subgroup M} (x : (quotient S)) {ε : ℝ} (hε : 0 < ε) :
  ∃ (m : M), quotient_add_group.mk' S m = x ∧ ∥m∥ < ∥x∥ + ε :=
begin
  obtain ⟨_, ⟨m : M, H : mk' S m = x, rfl⟩, hnorm : ∥m∥ < ∥x∥ + ε⟩ :=
    real.lt_Inf_add_pos (bdd_below_image_norm _) (image_norm_nonempty x) hε,
  subst H,
  exact ⟨m, rfl, hnorm⟩,
end

lemma norm_mk_lt' (S : add_subgroup M) (m : M) {ε : ℝ} (hε : 0 < ε) :
  ∃ s ∈ S, ∥m + s∥ < ∥mk' S m∥ + ε :=
begin
  obtain ⟨n : M, hn : mk' S n = mk' S m, hn' : ∥n∥ < ∥mk' S m∥ + ε⟩ :=
    norm_mk_lt (quotient_add_group.mk' S m) hε,
  erw [eq_comm, quotient_add_group.eq] at hn,
  use [- m + n, hn],
  rwa [add_neg_cancel_left]
end

lemma quotient_norm_add_le (S : add_subgroup M) (x y : quotient S) : ∥x + y∥ ≤ ∥x∥ + ∥y∥ :=
begin
  refine le_of_forall_pos_le_add (λ ε hε, _),
  replace hε := half_pos hε,
  obtain ⟨m, rfl, hm : ∥m∥ < ∥mk' S m∥ + ε / 2⟩ := norm_mk_lt x hε,
  obtain ⟨n, rfl, hn : ∥n∥ < ∥mk' S n∥ + ε / 2⟩ := norm_mk_lt y hε,
  calc ∥mk' S m + mk' S n∥ = ∥mk' S (m +  n)∥ : by rw (mk' S).map_add
  ... ≤ ∥m + n∥ : quotient_norm_mk_le S (m + n)
  ... ≤ ∥m∥ + ∥n∥ : norm_add_le _ _
  ... ≤ ∥mk' S m∥ + ∥mk' S n∥ + ε : by linarith
end

/-- The quotient norm of `0` is `0`. -/
lemma norm_mk_zero (S : add_subgroup M) : ∥(0 : (quotient S))∥ = 0 :=
begin
  erw quotient_norm_eq_zero_iff,
  exact subset_closure S.zero_mem
end

/-- If `(m : M)` has norm equal to `0` in `quotient S` for a closed subgroup `S` of `M`, then
`m ∈ S`. -/
lemma norm_zero_eq_zero (S : add_subgroup M) (hS : is_closed (S : set M)) (m : M)
  (h : ∥(quotient_add_group.mk' S) m∥ = 0) : m ∈ S :=
by rwa [quotient_norm_eq_zero_iff, hS.closure_eq] at h

lemma quotient_nhd_basis (S : add_subgroup M) :
  (𝓝 (0 : quotient S)).has_basis (λ ε : ℝ, 0 < ε) (λ ε, {x | ∥x∥ < ε}) :=
⟨begin
  intros U,
  split,
  { intros U_in,
    rw ← (mk' S).map_zero at U_in,
    have := preimage_nhds_coinduced U_in,
    rcases metric.mem_nhds_iff.mp this with ⟨ε, ε_pos, H⟩,
    use [ε/2, half_pos ε_pos],
    intros x x_in,
    dsimp at x_in,
    rcases norm_mk_lt x (half_pos ε_pos) with ⟨y, rfl, ry⟩,
    apply H,
    rw ball_0_eq,
    dsimp,
    linarith },
  { rintros ⟨ε, ε_pos, h⟩,
    have : (mk' S) '' (ball (0 : M) ε) ⊆ {x | ∥x∥ < ε},
    { rintros - ⟨x, x_in, rfl⟩,
      rw mem_ball_0_iff at x_in,
      exact lt_of_le_of_lt (quotient_norm_mk_le S x) x_in },
    apply filter.mem_sets_of_superset _ (set.subset.trans this h),
    clear h U this,
    apply mem_nhds_sets,
    { change is_open ((mk' S) ⁻¹' _),
      erw quotient_add_group.preimage_image_coe,
      apply is_open_Union,
      rintros ⟨s, s_in⟩,
      exact (continuous_add_right s).is_open_preimage _ is_open_ball },
    { exact ⟨(0 : M), mem_ball_self ε_pos, (mk' S).map_zero⟩ } },
end⟩

/-- The pseudometric space structure on the quotient by an additive subgroup. -/
noncomputable
instance add_subgroup.semi_normed_group_quotient (S : add_subgroup M) : semi_normed_group (quotient S) :=
{ dist               := λ x y, ∥x - y∥,
  dist_self          := λ x, by simp only [norm_mk_zero, sub_self],
  dist_comm          := quotient_norm_sub_rev,
  dist_triangle      := λ x y z,
begin
    unfold dist,
    have : x - z = (x - y) + (y - z) := by abel,
    rw this,
    exact quotient_norm_add_le S (x - y) (y - z)
  end,
  dist_eq := λ x y, rfl,
  to_uniform_space   := topological_add_group.to_uniform_space (quotient S),
  uniformity_dist    :=
  begin
    rw uniformity_eq_comap_nhds_zero',
    have := filter.has_basis.comap (λ (p : quotient S × quotient S), p.2 - p.1) (quotient_nhd_basis S),
    apply this.eq_of_same_basis,
    have : ∀ ε : ℝ, (λ (p : quotient S × quotient S), p.snd - p.fst) ⁻¹' {x | ∥x∥ < ε} =
      {p : quotient S × quotient S | ∥p.fst - p.snd∥ < ε},
    { intro ε,
      ext x,
      dsimp,
      rw quotient_norm_sub_rev },
    rw funext this,
    refine filter.has_basis_binfi_principal _ set.nonempty_Ioi,
    rintros ε (ε_pos : 0 < ε) η (η_pos : 0 < η),
    refine ⟨min ε η, lt_min ε_pos η_pos, _, _⟩,
    { suffices : ∀ (a b : quotient S), ∥a - b∥ < ε → ∥a - b∥ < η → ∥a - b∥ < ε, by simpa,
      exact λ a b h h', h },
    { simp }
  end }

-- This is a sanity check left here on purpose to ensure that potential refactors won't destroy
-- this important property.
example (S : add_subgroup M) : (quotient.topological_space : topological_space $ quotient S) =
S.semi_normed_group_quotient.to_uniform_space.to_topological_space :=
rfl

/-- The quotient in the category of normed groups. -/
noncomputable
instance add_subgroup.normed_group_quotient (S : add_subgroup M) [hS : is_closed (S : set M)] :
  normed_group (quotient S) :=
{ dist               := λ x y, ∥x - y∥,
  dist_self          := λ x, by simp only [norm_mk_zero, sub_self],
  dist_comm          := quotient_norm_sub_rev,
  dist_triangle      := λ x y z, by simpa only [dist, show x - z = (x - y) + (y - z), by abel] using
                                    quotient_norm_add_le S (x - y) (y - z),
  dist_eq := λ x y, rfl,
  to_uniform_space   := topological_add_group.to_uniform_space (quotient S),
  uniformity_dist    :=
  begin
    rw uniformity_eq_comap_nhds_zero',
    have := filter.has_basis.comap (λ (p : quotient S × quotient S), p.2 - p.1) (quotient_nhd_basis S),
    apply this.eq_of_same_basis,
    have : ∀ ε : ℝ, (λ (p : quotient S × quotient S), p.snd - p.fst) ⁻¹' {x | ∥x∥ < ε} =
      {p : quotient S × quotient S | ∥p.fst - p.snd∥ < ε},
    { intro ε,
      ext x,
      dsimp,
      rw quotient_norm_sub_rev },
    rw funext this,
    refine filter.has_basis_binfi_principal _ set.nonempty_Ioi,
    rintros ε (ε_pos : 0 < ε) η (η_pos : 0 < η),
    refine ⟨min ε η, lt_min ε_pos η_pos, _, _⟩,
    { suffices : ∀ (a b : quotient S), ∥a - b∥ < ε → ∥a - b∥ < η → ∥a - b∥ < ε, by simpa,
      exact λ a b h h', h },
    { simp }
  end,
  eq_of_dist_eq_zero :=
  begin
    rintros ⟨m⟩ ⟨m'⟩ (h : ∥mk' S m - mk' S m'∥ = 0),
    erw [← (mk' S).map_sub, quotient_norm_eq_zero_iff, hS.closure_eq,
         ← quotient_add_group.eq_iff_sub_mem] at h,
    exact h
  end }

-- This is a sanity check left here on purpose to ensure that potential refactors won't destroy
-- this important property.
example (S : add_subgroup M) [is_closed (S : set M)] :
  S.semi_normed_group_quotient = normed_group.to_semi_normed_group := rfl


namespace add_subgroup

open normed_group_hom

/-- The morphism from a seminormed group to the quotient by a subgroup. -/
noncomputable
def normed_mk (S : add_subgroup M) : normed_group_hom M (quotient S) :=
{ bound' := ⟨1, λ m, by simpa [one_mul] using quotient_norm_mk_le  _ m⟩,
  ..quotient_add_group.mk' S }

/-- `S.normed_mk` agrees with `quotient_add_group.mk' S`. -/
@[simp]
lemma normed_mk.apply (S : add_subgroup M) (m : M) : normed_mk S m = quotient_add_group.mk' S m :=
rfl

/-- `S.normed_mk` is surjective. -/
lemma surjective_normed_mk (S : add_subgroup M) : function.surjective (normed_mk S) :=
surjective_quot_mk _

/-- The kernel of `S.normed_mk` is `S`. -/
lemma ker_normed_mk (S : add_subgroup M) : S.normed_mk.ker = S :=
quotient_add_group.ker_mk  _

/-- The operator norm of the projection is at most `1`. -/
lemma norm_normed_mk_le (S : add_subgroup M) : ∥S.normed_mk∥ ≤ 1 :=
normed_group_hom.op_norm_le_bound _ zero_le_one (λ m, by simp [quotient_norm_mk_le])

/-- The operator norm of the projection is `1` if the subspace is not dense. -/
lemma norm_normed_mk (S : add_subgroup M) (h : (S.topological_closure : set M) ≠ univ) :
  ∥S.normed_mk∥ = 1 :=
begin
  obtain ⟨x, hx⟩ := set.nonempty_compl.2 h,
  let y := S.normed_mk x,
  have hy : ∥y∥ ≠ 0,
  { intro h0,
    exact set.not_mem_of_mem_compl hx ((quotient_norm_eq_zero_iff S x).1 h0) },
  refine le_antisymm (norm_normed_mk_le S) (le_of_forall_pos_le_add (λ ε hε, _)),
  suffices : 1 ≤ ∥S.normed_mk∥ + min ε ((1 : ℝ)/2),
  { exact le_add_of_le_add_left this (min_le_left ε ((1 : ℝ)/2)) },
  have hδ := sub_pos.mpr (lt_of_le_of_lt (min_le_right ε ((1 : ℝ)/2)) one_half_lt_one),
  have hδpos : 0 < min ε ((1 : ℝ)/2) := lt_min hε one_half_pos,
  have hδnorm := mul_pos (div_pos hδpos hδ) (lt_of_le_of_ne (norm_nonneg y) hy.symm),
  obtain ⟨m, hm, hlt⟩ := norm_mk_lt y hδnorm,
  have hrw : ∥y∥ + min ε (1 / 2) / (1 - min ε (1 / 2)) * ∥y∥ =
    ∥y∥ * (1 + min ε (1 / 2) / (1 - min ε (1 / 2))) := by ring,
  rw [hrw] at hlt,
  have hm0 : ∥m∥ ≠ 0,
  { intro h0,
    have hnorm := quotient_norm_mk_le S m,
    rw [h0, hm] at hnorm,
    replace hnorm := le_antisymm hnorm (norm_nonneg _),
    simpa [hnorm] using hy },
  replace hlt := (div_lt_div_right (lt_of_le_of_ne (norm_nonneg m) hm0.symm)).2 hlt,
  simp only [hm0, div_self, ne.def, not_false_iff] at hlt,
  have hrw₁ : ∥y∥ * (1 + min ε (1 / 2) / (1 - min ε (1 / 2))) / ∥m∥ =
    (∥y∥ / ∥m∥) * (1 + min ε (1 / 2) / (1 - min ε (1 / 2))) := by ring,
  rw [hrw₁] at hlt,
  replace hlt := (inv_pos_lt_iff_one_lt_mul (lt_trans (div_pos hδpos hδ) (lt_one_add _))).2 hlt,
  suffices : ∥S.normed_mk∥ ≥ 1 - min ε (1 / 2),
  { exact sub_le_iff_le_add.mp this },
  calc ∥S.normed_mk∥ ≥ ∥(S.normed_mk) m∥ / ∥m∥ : ratio_le_op_norm S.normed_mk m
  ...  = ∥y∥ / ∥m∥ : by rw [normed_mk.apply, hm]
  ... ≥ (1 + min ε (1 / 2) / (1 - min ε (1 / 2)))⁻¹ : le_of_lt hlt
  ... = 1 - min ε (1 / 2) : by field_simp [(ne_of_lt hδ).symm]
end

/-- The operator norm of the projection is `0` if the subspace is the whole space. -/
lemma norm_trivial_quotient_mk (S : add_subgroup M) (h : (S : set M) = set.univ) :
  ∥S.normed_mk∥ = 0 :=
begin
  refine le_antisymm (op_norm_le_bound _ (le_refl _) (λ x, _)) (norm_nonneg _),
  have hker : x ∈ (S.normed_mk).ker,
  { rw [S.ker_normed_mk],
    exact set.mem_of_eq_of_mem h trivial },
  rw [normed_group_hom.mem_ker _ x] at hker,
  rw [hker, zero_mul, norm_zero]
end

/-- `is_quotient f`, for `f : M ⟶ N` means that `N` is isomorphic to the quotient of `M`
by the kernel of `f`. -/
structure is_quotient (f : normed_group_hom M N) : Prop :=
(surjective : function.surjective f)
(norm : ∀ x, ∥f x∥ = Inf ((λ m, ∥x + m∥) '' f.ker))

/-- Given  `f : normed_group_hom M N` such that `f s = 0` for all `s ∈ S`, where,
`S : add_subgroup M` is closed, the induced morphism `normed_group_hom (quotient S) N`. -/
noncomputable
def lift {N : Type*} [semi_normed_group N] (S : add_subgroup M)
  (f : normed_group_hom M N) (hf : ∀ s ∈ S, f s = 0) :
  normed_group_hom (quotient S) N :=
{ bound' :=
  begin
    obtain ⟨c : ℝ≥0, hcpos : (0 : ℝ) < c, hc : f.bound_by c⟩ := f.bound,
    refine ⟨c, λ mbar, le_of_forall_pos_le_add (λ ε hε, _)⟩,
    obtain ⟨m : M, rfl : mk' S m = mbar, hmnorm : ∥m∥ < ∥mk' S m∥ + ε/c⟩ :=
      norm_mk_lt mbar (div_pos hε hcpos),
    calc ∥f m∥ ≤ c * ∥m∥ : hc m
    ... ≤ c*(∥mk' S m∥ + ε/c) : ((mul_lt_mul_left hcpos).mpr hmnorm).le
    ... = c * ∥mk' S m∥ + ε : by rw [mul_add, mul_div_cancel' _ hcpos.ne.symm]
  end,
  .. quotient_add_group.lift S f.to_add_monoid_hom hf }

lemma lift_mk  {N : Type*} [semi_normed_group N] (S : add_subgroup M)
  (f : normed_group_hom M N) (hf : ∀ s ∈ S, f s = 0) (m : M) :
  lift S f hf (S.normed_mk m) = f m := rfl

lemma lift_unique {N : Type*} [semi_normed_group N] (S : add_subgroup M)
  (f : normed_group_hom M N) (hf : ∀ s ∈ S, f s = 0)
  (g : normed_group_hom (quotient S) N) :
  g.comp (S.normed_mk) = f → g = lift S f hf :=
begin
  intro h,
  ext,
  rcases surjective_normed_mk _ x with ⟨x,rfl⟩,
  change (g.comp (S.normed_mk) x) = _,
  simpa only [h]
end

/-- `S.normed_mk` satisfies `is_quotient`. -/
lemma is_quotient_quotient (S : add_subgroup M) : is_quotient (S.normed_mk) :=
⟨S.surjective_normed_mk, λ m, by simpa [S.ker_normed_mk] using quotient_norm_mk_eq _ m⟩

lemma is_quotient.norm_lift {f : normed_group_hom M N} (hquot : is_quotient f) {ε : ℝ} (hε : 0 < ε)
  (n : N) : ∃ (m : M), f m = n ∧ ∥m∥ < ∥n∥ + ε :=
begin
  obtain ⟨m, rfl⟩ := hquot.surjective n,
  have nonemp : ((λ m', ∥m + m'∥) '' f.ker).nonempty,
  { rw set.nonempty_image_iff,
    exact ⟨0, is_add_submonoid.zero_mem⟩ },
  have bdd : bdd_below ((λ m', ∥m + m'∥) '' f.ker),
  { use 0,
    rintro _ ⟨x, hx, rfl⟩,
    apply norm_nonneg },
  rcases real.lt_Inf_add_pos bdd nonemp hε with
    ⟨_, ⟨⟨x, hx, rfl⟩, H : ∥m + x∥ < Inf ((λ (m' : M), ∥m + m'∥) '' f.ker) + ε⟩⟩,
  exact ⟨m+x, by rw [f.map_add,(normed_group_hom.mem_ker f x).mp hx, add_zero],
               by rwa hquot.norm⟩,
end

lemma is_quotient.norm_le {f : normed_group_hom M N} (hquot : is_quotient f) (m : M) : ∥f m∥ ≤ ∥m∥ :=
begin
  rw hquot.norm,
  apply real.Inf_le,
  { use 0,
    rintros _ ⟨m', hm', rfl⟩,
    apply norm_nonneg },
  { exact ⟨0, f.ker.zero_mem, by simp⟩ }
end

end add_subgroup
