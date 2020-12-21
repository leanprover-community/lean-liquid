import locally_constant.algebra
import analysis.normed_space.basic

noncomputable theory

-- move this
section for_mathlib

lemma real.Sup_exists_of_finite (s : set ℝ) (hs : s.finite) :
  ∃ (x : ℝ), ∀ (y : ℝ), y ∈ s → y ≤ x :=
begin
  rcases hs.exists_finset with ⟨t, ht⟩,
  use t.fold max 0 id,
  intros y hy,
  exact (finset.fold_op_rel_iff_or (@le_max_iff _ _)).mpr (or.inr ⟨y, by rwa ht, le_rfl⟩)
end

end for_mathlib

namespace locally_constant

variables {X Y : Type*} [topological_space X]

/-- The sup norm on locally constant function -/
protected def has_norm [has_norm Y] : has_norm (locally_constant X Y) :=
{ norm := λ f, ⨆ x, ∥f x∥ }

/-- The sup edist on locally constant function -/
protected def has_edist [has_edist Y] : has_edist (locally_constant X Y) :=
{ edist := λ f g, ⨆ x, edist (f x) (g x) }

/-- The sup edist on locally constant function -/
protected def has_dist [has_dist Y] : has_dist (locally_constant X Y) :=
{ dist := λ f g, ⨆ x, dist (f x) (g x) }

local attribute [instance]
  locally_constant.has_norm
  locally_constant.has_edist
  locally_constant.has_dist

lemma edist_apply_le [has_edist Y] (f g : locally_constant X Y) (x : X) :
  edist (f x) (g x) ≤ edist f g :=
le_Sup (set.mem_range_self x)

section compact_domain

variables [compact_space X]

lemma norm_apply_le [has_norm Y] (f : locally_constant X Y) (x : X) :
  ∥f x∥ ≤ ∥f∥ :=
begin
  refine real.le_Sup _ _ (set.mem_range_self _),
  apply real.Sup_exists_of_finite,
  rw set.range_comp,
  exact f.range_finite.image _
end

lemma exists_ub_range_dist [has_dist Y] (f g : locally_constant X Y) :
  ∃ x : ℝ, ∀ y : ℝ, y ∈ set.range (λ (x : X), dist (f x) (g x)) → y ≤ x :=
begin
  apply real.Sup_exists_of_finite,
  simp only [← function.uncurry_apply_pair dist],
  rw set.range_comp,
  apply set.finite.image,
  apply (f.range_finite.prod g.range_finite).subset,
  rintro ⟨y₁, y₂⟩,
  simp only [set.mem_range, prod.mk.inj_iff],
  rintro ⟨y, rfl, rfl⟩,
  simp only [set.mem_range_self, set.prod_mk_mem_set_prod_eq, and_self]
end

lemma dist_apply_le [has_dist Y] (f g : locally_constant X Y) (x : X) :
  dist (f x) (g x) ≤ dist f g :=
real.le_Sup _ (exists_ub_range_dist _ _) (set.mem_range_self x)

-- consider giving the `edist` and the `uniform_space` explicitly
/-- The metric space on locally constant functions on a compact space, with sup distance. -/
protected def metric_space [metric_space Y] : metric_space (locally_constant X Y) :=
{ dist_self := λ f, show (⨆ x, dist (f x) (f x)) = 0,
    begin
      simp only [dist_self, supr],
      by_cases H : nonempty X, swap,
      { rwa [set.range_eq_empty.mpr H, real.Sup_empty] },
      resetI,
      simp only [set.range_const, cSup_singleton]
    end,
  eq_of_dist_eq_zero :=
  begin
    intros f g h,
    ext x,
    apply eq_of_dist_eq_zero,
    apply le_antisymm _ dist_nonneg,
    rw ← h,
    exact dist_apply_le _ _ _
  end,
  dist_comm := λ f g, show Sup _ = Sup _, by { simp only [dist_comm] },
  dist_triangle :=
  begin
    intros f g h,
    by_cases H : nonempty X, swap,
    { show Sup _ ≤ Sup _ + Sup _, simp only [set.range_eq_empty.mpr H, real.Sup_empty, add_zero] },
    refine (real.Sup_le _ _ (exists_ub_range_dist _ _)).mpr _,
    { obtain ⟨x⟩ := H, exact ⟨_, set.mem_range_self x⟩ },
    rintro r ⟨x, rfl⟩,
    calc dist (f x) (h x) ≤ dist (f x) (g x) + dist (g x) (h x) : dist_triangle _ _ _
    ... ≤ dist f g + dist g h : add_le_add (dist_apply_le _ _ _) (dist_apply_le _ _ _)
  end,
  .. locally_constant.has_dist }

/-- The metric space on locally constant functions on a compact space, with sup distance. -/
protected def normed_group {G : Type*} [normed_group G] : normed_group (locally_constant X G) :=
{ dist_eq := λ f g, show Sup _ = Sup _,
    by simp only [normed_group.dist_eq, locally_constant.sub_apply],
  .. locally_constant.has_norm, .. locally_constant.add_comm_group,
  .. locally_constant.metric_space }

end compact_domain

end locally_constant
