import analysis.normed_space.basic
import topology.sequences
open_locale nnreal big_operators

/-!
# Normed groups homomorphisms

This file gathers definitions and elementary constructions about bounded group homormorphisms
between normed groups (abreviated to "normed group homs").

The main lemmas relate the boundedness condition to continuity and Lispschitzness.

The main construction is to endow the type of normed group homs between two given normed group
with a group structure and a norm (we haven't proved yet that these two make a normed group
structure).

Some easy other constructions are related to subgroups of normed groups.
-/

set_option old_structure_cmd true

/-- A morphism of normed abelian groups is a bounded group homomorphism. -/
structure normed_group_hom (V W : Type*) [normed_group V] [normed_group W]
  extends add_monoid_hom V W :=
(bound' : ∃ C, ∀ v, ∥to_fun v∥ ≤ C * ∥v∥)

attribute [nolint doc_blame] normed_group_hom.mk
attribute [nolint doc_blame] normed_group_hom.to_add_monoid_hom

namespace normed_group_hom

-- initialize_simps_projections normed_group_hom (to_fun → apply)

variables {V V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group V₁] [normed_group V₂] [normed_group V₃]
variables (f g : normed_group_hom V₁ V₂)

instance : has_coe_to_fun (normed_group_hom V₁ V₂) := ⟨_, normed_group_hom.to_fun⟩

@[simp] lemma coe_mk (f) (h₁) (h₂) (h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : normed_group_hom V₁ V₂) = f := rfl

@[simp] lemma mk_to_monoid_hom (f) (h₁) (h₂) (h₃) :
  (⟨f, h₁, h₂, h₃⟩ : normed_group_hom V₁ V₂).to_add_monoid_hom = ⟨f, h₁, h₂⟩ := rfl

@[simp] lemma map_zero : f 0 = 0 := f.to_add_monoid_hom.map_zero

@[simp] lemma map_add (x y) : f (x + y) = f x + f y := f.to_add_monoid_hom.map_add _ _

@[simp] lemma map_sum {ι : Type*} (v : ι → V₁) (s : finset ι) :
  f (∑ i in s, v i) = ∑ i in s, f (v i) :=
f.to_add_monoid_hom.map_sum _ _

@[simp] lemma map_sub (x y) : f (x - y) = f x - f y := f.to_add_monoid_hom.map_sub _ _

@[simp] lemma map_neg (x) : f (-x) = -(f x) := f.to_add_monoid_hom.map_neg _

/-- Make a normed group hom from a group hom and a norm bound. -/
def mk' (f : V₁ →+ V₂) (C : ℝ≥0) (hC : ∀ x, ∥f x∥ ≤ C * ∥x∥) : normed_group_hom V₁ V₂ :=
{ bound' := ⟨C, hC⟩ .. f}

@[simp] lemma coe_mk' (f : V₁ →+ V₂) (C) (hC) : ⇑(mk' f C hC) = f := rfl

/-- Predicate asserting a norm bound on a normed group hom. -/
def bound_by (f : normed_group_hom V₁ V₂) (C : ℝ≥0) : Prop := ∀ x, ∥f x∥ ≤ C * ∥x∥

lemma mk'_bound_by (f : V₁ →+ V₂) (C) (hC) : (mk' f C hC).bound_by C := hC

lemma bound : ∃ C, 0 < C ∧ f.bound_by C :=
begin
  obtain ⟨C, hC⟩ := f.bound',
  let C' : ℝ≥0 := ⟨max C 1, le_max_right_of_le zero_le_one⟩,
  use C',
  simp only [C', ← nnreal.coe_lt_coe, subtype.coe_mk, nnreal.coe_zero,
    lt_max_iff, zero_lt_one, or_true, true_and],
  intro v,
  calc ∥f v∥
      ≤ C * ∥v∥ : hC v
  ... ≤ max C 1 * ∥v∥ : mul_le_mul (le_max_left _ _) le_rfl (norm_nonneg _) _,
  exact zero_le_one.trans (le_max_right _ _)
end

lemma lipschitz_of_bound_by (C : ℝ≥0) (h : f.bound_by C) :
  lipschitz_with (nnreal.of_real C) f :=
lipschitz_with.of_dist_le' $ λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

theorem antilipschitz_of_bound_by {K : ℝ≥0} (h : ∀ x, ∥x∥ ≤ K * ∥f x∥) :
  antilipschitz_with K f :=
antilipschitz_with.of_le_mul_dist $
λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

protected lemma uniform_continuous (f : normed_group_hom V₁ V₂) :
  uniform_continuous f :=
begin
  obtain ⟨C, C_pos, hC⟩ := f.bound,
  exact (lipschitz_of_bound_by f C hC).uniform_continuous
end

@[continuity]
protected lemma continuous (f : normed_group_hom V₁ V₂) : continuous f :=
f.uniform_continuous.continuous

variables {f g}

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

instance : has_zero (normed_group_hom V₁ V₂) :=
⟨{ bound' := ⟨0, λ v, show ∥(0 : V₂)∥ ≤ 0 * _, by rw [norm_zero, zero_mul]⟩,
   .. (0 : V₁ →+ V₂) }⟩

instance : inhabited (normed_group_hom V₁ V₂) := ⟨0⟩

lemma coe_inj ⦃f g : normed_group_hom V₁ V₂⦄ (h : (f : V₁ → V₂) = g) : f = g :=
by cases f; cases g; cases h; refl

/-- The identity as a continuous normed group hom. -/
@[simps]
def id : normed_group_hom V V :=
{ bound' := ⟨1, λ v, show ∥v∥ ≤ 1 * ∥v∥, by rw [one_mul]⟩,
  .. add_monoid_hom.id V }

/-- The composition of continuous normed group homs. -/
@[simps]
def comp (g : normed_group_hom V₂ V₃) (f : normed_group_hom V₁ V₂) :
  normed_group_hom V₁ V₃ :=
{ bound' :=
  begin
    obtain ⟨Cf, Cf_pos, hf⟩ := f.bound,
    obtain ⟨Cg, Cg_pos, hg⟩ := g.bound,
    use [Cg * Cf],
    assume v,
    calc ∥g (f v)∥
        ≤ Cg * ∥f v∥    : hg _
    ... ≤ Cg * Cf * ∥v∥ : _,
    rw mul_assoc,
    exact mul_le_mul le_rfl (hf v) (norm_nonneg _) Cg_pos.le
  end
  .. g.to_add_monoid_hom.comp f.to_add_monoid_hom }

/-- Addition of normed group homs. -/
instance : has_add (normed_group_hom V₁ V₂) :=
⟨λ f g,
{ bound' :=
  begin
    obtain ⟨Cf, Cf_pos, hCf⟩ := f.bound,
    obtain ⟨Cg, Cg_pos, hCg⟩ := g.bound,
    use [Cf + Cg],
    assume v,
    calc ∥f v + g v∥
        ≤ ∥f v∥ + ∥g v∥ : norm_add_le _ _
    ... ≤ Cf * ∥v∥ + Cg * ∥v∥ : add_le_add (hCf _) (hCg _)
    ... = (Cf + Cg) * ∥v∥ : by rw add_mul
  end,
  .. (f.to_add_monoid_hom + g.to_add_monoid_hom) }⟩

/-- Opposite of a normed group hom. -/
instance : has_neg (normed_group_hom V₁ V₂) :=
⟨λ f,
{ bound' :=
  begin
    obtain ⟨C, C_pos, hC⟩ := f.bound,
    use C,
    assume v,
    calc ∥-(f v)∥
        = ∥f v∥ : norm_neg _
    ... ≤ C * ∥v∥ : hC _
  end, .. (-f.to_add_monoid_hom) }⟩

/-- Subtraction of normed group homs. -/
instance : has_sub (normed_group_hom V₁ V₂) :=
⟨λ f g,
{ bound' :=
  begin
    simp only [add_monoid_hom.sub_apply, add_monoid_hom.to_fun_eq_coe, sub_eq_add_neg],
    exact (f + -g).bound'
  end,
  .. (f.to_add_monoid_hom - g.to_add_monoid_hom) }⟩

@[simp] lemma coe_zero : ⇑(0 : normed_group_hom V₁ V₂) = 0 := rfl

@[simp] lemma coe_neg (f : normed_group_hom V₁ V₂) : ⇑(-f) = -f := rfl

@[simp] lemma coe_add (f g : normed_group_hom V₁ V₂) : ⇑(f + g) = f + g := rfl

@[simp] lemma coe_sub (f g : normed_group_hom V₁ V₂) : ⇑(f - g) = f - g := rfl

/-- Homs between two given normed groups form a commutative additive group. -/
instance : add_comm_group (normed_group_hom V₁ V₂) :=
by refine_struct
{ .. normed_group_hom.has_add, .. normed_group_hom.has_zero,
  .. normed_group_hom.has_neg, ..normed_group_hom.has_sub };
{ intros, ext, simp [add_assoc, add_comm, add_left_comm, sub_eq_add_neg] }
.

/-- The norm of a normed groups hom. -/
noncomputable instance : has_norm (normed_group_hom V₁ V₂) :=
⟨λ f, ↑(⨅ (r : ℝ≥0) (h : f.bound_by r), r)⟩

/-- Composition of normed groups hom as an additive group morphism. -/
def comp_hom : (normed_group_hom V₂ V₃) →+ (normed_group_hom V₁ V₂) →+ (normed_group_hom V₁ V₃) :=
add_monoid_hom.mk' (λ g, add_monoid_hom.mk' (λ f, g.comp f)
  (by { intros, ext, exact g.map_add _ _ }))
  (by { intros, ext, refl })

@[simp] lemma comp_zero (f : normed_group_hom V₂ V₃) : f.comp (0 : normed_group_hom V₁ V₂) = 0 :=
by { ext, exact f.map_zero' }

@[simp] lemma zero_comp (f : normed_group_hom V₁ V₂) : (0 : normed_group_hom V₂ V₃).comp f = 0 :=
by { ext, refl }

@[simp] lemma sum_apply {ι : Type*} (s : finset ι) (f : ι → normed_group_hom V₁ V₂) (v : V₁) :
  (∑ i in s, f i) v = ∑ i in s, (f i v) :=
begin
  classical,
  apply finset.induction_on s,
  { simp only [coe_zero, finset.sum_empty, pi.zero_apply] },
  { intros i s his IH,
    simp only [his, IH, pi.add_apply, finset.sum_insert, not_false_iff, coe_add] }
end

end normed_group_hom

namespace normed_group_hom

section kernels

variables {V V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group V₁] [normed_group V₂] [normed_group V₃]
variables (f : normed_group_hom V₁ V₂) (g : normed_group_hom V₂ V₃)

/-- The kernel of a bounded group homomorphism. Naturally endowed with a `normed_group` instance. -/
def ker : add_subgroup V₁ := f.to_add_monoid_hom.ker

/-- The normed group structure on the kernel of a normed group hom. -/
instance : normed_group f.ker :=
{ dist_eq := λ v w, dist_eq_norm _ _ }

lemma mem_ker (v : V₁) : v ∈ f.ker ↔ f v = 0 :=
by { erw f.to_add_monoid_hom.mem_ker, refl }

/-- The inclusion of the kernel, as bounded group homomorphism. -/
@[simps] def ker.incl : normed_group_hom f.ker V₁ :=
{ to_fun := (coe : f.ker → V₁),
  map_zero' := add_subgroup.coe_zero _,
  map_add' := λ v w, add_subgroup.coe_add _ _ _,
  bound' := ⟨1, λ v, by { rw [one_mul], refl }⟩ }

/-- Given a normed group hom `f : V₁ → V₂` satisfying `g.comp f = 0` for some `g : V₂ → V₃`,
    the corestriction of `f` to the kernel of `g`. -/
@[simps] def ker.lift (h : g.comp f = 0) :
  normed_group_hom V₁ g.ker :=
{ to_fun := λ v, ⟨f v, by { erw g.mem_ker, show (g.comp f) v = 0, rw h, refl }⟩,
  map_zero' := by { simp only [map_zero], refl },
  map_add' := λ v w, by { simp only [map_add], refl },
  bound' := f.bound' }

@[simp] lemma ker.incl_comp_lift (h : g.comp f = 0) :
  (ker.incl g).comp (ker.lift f g h) = f :=
by { ext, refl }

end kernels

section range

variables {V V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group V₁] [normed_group V₂] [normed_group V₃]
variables (f : normed_group_hom V₁ V₂) (g : normed_group_hom V₂ V₃)

/-- The image of a bounded group homomorphism. Naturally endowed with a `normed_group` instance. -/
def range : add_subgroup V₂ := f.to_add_monoid_hom.range

lemma mem_range (v : V₂) : v ∈ f.range ↔ ∃ w, f w = v :=
by { rw [range, add_monoid_hom.mem_range], refl }

end range

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
  have Scom : is_complete (S : set M) := complete_space_coe_iff_is_complete.mp _inst_3,
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

variables {V W V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group W]
variables [normed_group V₁] [normed_group V₂] [normed_group V₃]
variables {f : normed_group_hom V W}

/-- A `normed_group_hom` is *norm-nonincreasing* if `∥f v∥ ≤ ∥v∥` for all `v`. -/
def norm_noninc (f : normed_group_hom V W) : Prop :=
∀ v, ∥f v∥ ≤ ∥v∥

/-- A strict `normed_group_hom` is a `normed_group_hom` that preserves the norm. -/
def is_strict (f : normed_group_hom V W) : Prop :=
∀ v, ∥f v∥ = ∥v∥

namespace norm_noninc

lemma bound_by_one (hf : f.norm_noninc) : f.bound_by 1 :=
λ v, by simpa only [one_mul, nnreal.coe_one] using hf v

lemma id : (id : normed_group_hom V V).norm_noninc :=
λ v, le_rfl

lemma comp {g : normed_group_hom V₂ V₃} {f : normed_group_hom V₁ V₂}
  (hg : g.norm_noninc) (hf : f.norm_noninc) :
  (g.comp f).norm_noninc :=
λ v, (hg (f v)).trans (hf v)

end norm_noninc

namespace is_strict

lemma injective (hf : f.is_strict) :
  function.injective f :=
begin
  intros x y h,
  rw ← sub_eq_zero at *,
  suffices : ∥ x - y ∥ = 0, by simpa,
  rw ← hf,
  simpa,
end

lemma norm_noninc (hf : f.is_strict) : f.norm_noninc :=
λ v, le_of_eq $ hf v

lemma bound_by_one (hf : f.is_strict) : f.bound_by 1 :=
hf.norm_noninc.bound_by_one

lemma id : (id : normed_group_hom V V).is_strict :=
λ v, rfl

lemma comp {g : normed_group_hom V₂ V₃} {f : normed_group_hom V₁ V₂}
  (hg : g.is_strict) (hf : f.is_strict) :
  (g.comp f).is_strict :=
λ v, (hg (f v)).trans (hf v)

end is_strict

end normed_group_hom

#lint- only unused_arguments def_lemma doc_blame
