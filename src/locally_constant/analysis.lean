import topology.locally_constant.algebra
import analysis.normed_space.normed_group_hom

import for_mathlib.normed_group_hom_bound_by

/-!
# Analysis of locally constant maps

This file defines the normed group of locally constant maps from a compact topological
space into a normed group (with the sup norm).

## Main construction

* The instance `locally_constant.normed_group`
* `locally_constant.map_hom`: push-forward of locally constant maps as a normed group hom
* `locally_constant.comap_hom`: pull-back of locally constant maps as a normed group hom
-/

noncomputable theory
open_locale nnreal

open set

-- move this
section for_mathlib

lemma set.range_pair_subset_range {α β γ : Type*} (f : α → β) (g : α → γ) :
  range (λ x, (f x, g x)) ⊆ (range f).prod (range g) :=
begin
  rw [show (λ x, (f x, g x)) = prod.map f g ∘ (λ x, (x, x)), from funext (λ x, rfl),
      ← range_prod_map],
  apply range_comp_subset_range
end

-- feel free to golf!!
lemma real.Sup_mul (r : ℝ) (s : set ℝ) (hr : 0 < r) :
  Sup ({x | ∃ y ∈ s, r * y = x}) = r * Sup s :=
begin
  let P₁ : Prop := (∃ (x : ℝ), x ∈ {x : ℝ | ∃ (y : ℝ) (H : y ∈ s), r * y = x}) ∧
    ∃ (x : ℝ), ∀ (y : ℝ), y ∈ {x : ℝ | ∃ (y : ℝ) (H : y ∈ s), r * y = x} → y ≤ x,
  let P₂ : Prop := (∃ (x : ℝ), x ∈ s) ∧ ∃ (x : ℝ), ∀ (y : ℝ), y ∈ s → y ≤ x,
  have H : P₁ ↔ P₂ := _,
  { by_cases h : P₁,
    { apply le_antisymm,
      { rw real.Sup_le _ h.1 h.2,
        rintro _ ⟨x, hx, rfl⟩,
        apply mul_le_mul_of_nonneg_left _ hr.le,
        rw H at h,
        exact real.le_Sup _ h.2 hx },
      { rw H at h,
        rw [← le_div_iff' hr, real.Sup_le _ h.1 h.2],
        intros x hx,
        rw le_div_iff' hr,
        rw ← H at h,
        exact real.le_Sup _ h.2 ⟨_, hx, rfl⟩ } },
    { simp only [real.Sup_def],
      classical,
      rw [dif_neg, dif_neg, mul_zero],
      { rw H at h, exact h }, { exact h } } },
  { apply and_congr,
    { simp only [exists_prop, set.mem_set_of_eq],
      rw exists_comm,
      simp only [and_comm, exists_eq_left'] },
    { simp only [exists_prop, set.mem_set_of_eq, and_comm],
      simp only [exists_eq_left', mul_comm r, ← div_eq_iff_mul_eq hr.ne.symm],
      split; rintro ⟨x, hx⟩,
      { refine ⟨x / r, λ y hy, _⟩,
        rw ← mul_div_cancel y hr.ne.symm at hy,
        rw le_div_iff hr,
        exact hx _ hy },
      { refine ⟨r * x, λ y hy, _⟩,
        rw ← div_le_iff' hr,
        exact hx _ hy } } },
end

end for_mathlib

open set

namespace locally_constant

variables {X Y Z V V₁ V₂ V₃ : Type*} [topological_space X]

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

lemma norm_def [has_norm Y] (f : locally_constant X Y) : ∥f∥ = ⨆ x, ∥f x∥ := rfl

lemma edist_def [has_edist Y] (f g : locally_constant X Y) :
  edist f g = ⨆ x, edist (f x) (g x) := rfl

lemma dist_def [has_dist Y] (f g : locally_constant X Y) : dist f g = ⨆ x, dist (f x) (g x) := rfl

section compact_domain

variables [compact_space X]

lemma norm_apply_le [has_norm Y] (f : locally_constant X Y) (x : X) :
  ∥f x∥ ≤ ∥f∥ :=
begin
  refine real.le_Sup _ _ (set.mem_range_self _),
  apply exists_upper_bound_image,
  rw range_comp,
  exact f.range_finite.image _
end

lemma exists_ub_range_dist [has_dist Y] (f g : locally_constant X Y) :
  ∃ x : ℝ, ∀ y : ℝ, y ∈ set.range (λ (x : X), dist (f x) (g x)) → y ≤ x :=
begin
  apply exists_upper_bound_image,
  simp only [← function.uncurry_apply_pair dist],
  rw range_comp,
  apply finite.image,
  apply (f.range_finite.prod g.range_finite).subset,
  apply range_pair_subset_range,
end

lemma dist_apply_le [has_dist Y] (f g : locally_constant X Y) (x : X) :
  dist (f x) (g x) ≤ dist f g :=
real.le_Sup _ (exists_ub_range_dist _ _) (set.mem_range_self x)

-- consider giving the `edist` and the `uniform_space` explicitly
/-- The metric space on locally constant functions on a compact space, with sup distance. -/
protected def pseudo_metric_space [pseudo_metric_space Y] :
  pseudo_metric_space (locally_constant X Y) :=
{ dist_self := λ f, show (⨆ x, dist (f x) (f x)) = 0,
    begin
      simp only [dist_self, supr],
      by_cases H : nonempty X, swap,
      { rwa [set.range_eq_empty.mpr H, real.Sup_empty] },
      resetI,
      simp only [set.range_const, cSup_singleton]
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


/--
The seminormed group of locally constant functions from a compact space to a seminormed group.
-/
protected def semi_normed_group {G : Type*} [semi_normed_group G] :
  semi_normed_group (locally_constant X G) :=
{ dist_eq := λ f g, show Sup _ = Sup _,
  by simp only [semi_normed_group.dist_eq, locally_constant.sub_apply],
  .. locally_constant.has_norm, .. locally_constant.add_comm_group,
  .. locally_constant.pseudo_metric_space }

/-- The normed group of locally constant functions from a compact space to a normed group. -/
protected def normed_group {G : Type*} [normed_group G] : normed_group (locally_constant X G) :=
{ .. locally_constant.semi_normed_group,
  .. locally_constant.metric_space }

local attribute [instance] locally_constant.semi_normed_group

section map_hom

variables [semi_normed_group V] [semi_normed_group V₁] [semi_normed_group V₂] [semi_normed_group V₃]

/-- Push-forward of locally constant maps under a normed group hom, as a normed
group hom between types of locally constant functions. -/
@[simps]
def map_hom (f : normed_group_hom V₁ V₂) :
  normed_group_hom (locally_constant X V₁) (locally_constant X V₂) :=
{ to_fun := locally_constant.map f,
  map_add' := by { intros x y, ext s, apply f.map_add' },
  bound' :=
  begin
    obtain ⟨C, C_pos, hC⟩ := f.bound,
    use C,
    rintro (g : locally_constant _ _),
    calc Sup (set.range (λ x, ∥f (g x)∥))
        ≤ Sup (set.range (λ x, C * ∥g x∥)) : _
    ... = C * Sup (set.range (λ x, ∥g x∥)) : _,
    { by_cases H : nonempty X, swap,
      { simp only [set.range_eq_empty.mpr H, real.Sup_empty] },
      apply real.Sup_le_ub,
      { obtain ⟨x⟩ := H, exact ⟨_, set.mem_range_self x⟩ },
      rintro _ ⟨x, rfl⟩,
      calc ∥f (g x)∥ ≤ C * ∥g x∥ : hC _
      ... ≤ Sup _ : real.le_Sup _ _ _,
      { apply exists_upper_bound_image,
        rw [set.range_comp, set.range_comp],
        exact (g.range_finite.image _).image _ },
      { exact set.mem_range_self _ } },
    { convert real.Sup_mul C _ C_pos using 2,
      ext x,
      simp only [set.mem_range, exists_prop, set.set_of_mem_eq, exists_exists_eq_and],
      simp only [set.mem_set_of_eq] }
  end }

@[simp] lemma map_hom_id :
  @map_hom X _ _ _ _ _ _ (@normed_group_hom.id V _) = normed_group_hom.id :=
by { ext, refl }

@[simp] lemma map_hom_comp (g : normed_group_hom V₂ V₃) (f : normed_group_hom V₁ V₂) :
  (@map_hom X _ _ _ _ _ _ g).comp (map_hom f) = map_hom (g.comp f) :=
by { ext, refl }

lemma map_hom_bound_by (C : ℝ≥0) (hC : 0 < C) {f : normed_group_hom V₁ V₂} (hf : f.bound_by C) :
  (@map_hom X _ _ _ _ _ _ f).bound_by C :=
begin
  rintro (g : locally_constant _ _),
  calc Sup (set.range (λ x, ∥f (g x)∥))
      ≤ Sup (set.range (λ x, C * ∥g x∥)) : _
  ... = C * Sup (set.range (λ x, ∥g x∥)) : _,
  { by_cases H : nonempty X, swap,
    { simp only [set.range_eq_empty.mpr H, real.Sup_empty] },
    apply real.Sup_le_ub,
    { obtain ⟨x⟩ := H, exact ⟨_, set.mem_range_self x⟩ },
    rintro _ ⟨x, rfl⟩,
    calc ∥f (g x)∥ ≤ C * ∥g x∥ : hf _
    ... ≤ Sup _ : real.le_Sup _ _ _,
    { apply exists_upper_bound_image,
      rw [set.range_comp, set.range_comp],
      exact (g.range_finite.image _).image _ },
    { exact set.mem_range_self _ } },
  { convert real.Sup_mul C _ hC using 2,
    ext x,
    simp only [set.mem_range, exists_prop, set.set_of_mem_eq, exists_exists_eq_and],
    simp only [set.mem_set_of_eq] }
end

end map_hom

section comap_hom
/-!
### comapping as normed_group_hom
-/

variables [topological_space Y] [compact_space Y] [topological_space Z] [compact_space Z]
variables [semi_normed_group V]

/-- Pull-back of locally constant maps under a normed group hom, as a normed
group hom between types of locally constant functions. -/
@[simps]
def comap_hom (f : X → Y) (hf : continuous f) :
  normed_group_hom (locally_constant Y V) (locally_constant X V) :=
add_monoid_hom.mk_normed_group_hom'
  (add_monoid_hom.mk'
    (locally_constant.comap f)
    (by { intros, ext, simp only [hf, add_apply, function.comp_app, coe_comap] }))
  1
  begin
    assume g,
    rw one_mul,
    show Sup _ ≤ Sup _,
    simp only [hf, function.comp_app, coe_comap, add_monoid_hom.mk'_apply],
    by_cases hX : nonempty X, swap,
    { simp only [set.range_eq_empty.mpr hX, real.Sup_empty],
      by_cases hY : nonempty Y, swap,
      { simp only [set.range_eq_empty.mpr hY, real.Sup_empty] },
      obtain ⟨y⟩ := hY,
      calc 0 ≤ ∥g y∥ : norm_nonneg _
         ... ≤ _ : _,
      apply real.le_Sup,
      { apply exists_upper_bound_image,
        rw set.range_comp,
        exact g.range_finite.image _ },
      { exact set.mem_range_self _ } },
    rw real.Sup_le,
    { rintro _ ⟨x, rfl⟩,
      apply real.le_Sup,
      { apply exists_upper_bound_image,
        rw set.range_comp,
        exact g.range_finite.image _ },
      { exact set.mem_range_self _ } },
    { obtain ⟨x⟩ := hX,
      exact ⟨_, set.mem_range_self x⟩ },
    { { apply exists_upper_bound_image,
        rw [set.range_comp, set.range_comp],
        apply set.finite.image,
        apply g.range_finite.subset,
        apply set.image_subset_range } }
  end

@[simp] lemma comap_hom_id : @comap_hom X X V _ _ _ _ _ id continuous_id = normed_group_hom.id :=
begin
  ext,
  simp only [comap_id, comap_hom_apply, id.def, normed_group_hom.id_apply,
    add_monoid_hom.to_fun_eq_coe, add_monoid_hom.id_apply]
end

@[simp] lemma comap_hom_comp (f : X → Y) (g : Y → Z) (hf : continuous f) (hg : continuous g) :
  (@comap_hom _ _ V _ _ _ _ _ f hf).comp (comap_hom g hg) = (comap_hom (g ∘ f) (hg.comp hf)) :=
begin
  ext φ x,
  -- `[simps]` is producing bad lemmas... I don't know how to trick it into creating good ones
  -- so we use `show` instead, to get into a defeq shape that is usable
  show (comap_hom f hf) ((comap_hom g hg) φ) x = _,
  simp only [hg.comp hf, hf, hg, comap_hom_apply, coe_comap]
end

lemma comap_hom_bound_by (f : X → Y) (hf : continuous f) :
  (@comap_hom _ _ V _ _ _ _ _ f hf).bound_by 1 :=
normed_group_hom.mk_normed_group_hom'_bound_by _ _ _

lemma comap_hom_norm_noninc (f : X → Y) (hf : continuous f) :
  (@comap_hom _ _ V _ _ _ _ _ f hf).norm_noninc :=
(comap_hom_bound_by f hf).norm_noninc

end comap_hom

end compact_domain

end locally_constant

#lint- only unused_arguments def_lemma doc_blame
