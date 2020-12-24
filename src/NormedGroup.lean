import analysis.normed_space.basic
import algebra.punit_instances
import category_theory.concrete_category.bundled_hom
import category_theory.limits.shapes.zero

/-!
# The category of normed abelian groups and continuous group homomorphisms

-/

universes u v

-- move this
section for_mathlib

instance punit.uniform_space : uniform_space punit := ⊥

noncomputable
instance punit.metric_space : metric_space punit :=
{ dist := λ _ _, 0,
  dist_self := λ _, rfl,
  dist_comm := λ _ _, rfl,
  eq_of_dist_eq_zero := λ _ _ _, subsingleton.elim _ _,
  dist_triangle := λ _ _ _, show (0:ℝ) ≤ 0 + 0, by rw add_zero,
  .. punit.uniform_space }

noncomputable
instance punit.normed_group : normed_group punit :=
{ norm := function.const _ 0,
  dist_eq := λ _ _, rfl,
  .. punit.add_comm_group, .. punit.metric_space }

end for_mathlib

open category_theory

/-- The category of normed abelian groups and bounded group homomorphisms. -/
def NormedGroup : Type (u+1) := bundled normed_group

set_option old_structure_cmd true

/-- A morphism of normed abelian groups is a bounded group homomorphism. -/
structure normed_group_hom (V W : Type*) [normed_group V] [normed_group W]
  extends add_monoid_hom V W :=
(bound' : ∃ C, ∀ v, ∥to_fun v∥ ≤ C * ∥v∥)

namespace normed_group_hom

variables {V V₁ V₂ V₃ : Type*}
variables [normed_group V] [normed_group V₁] [normed_group V₂] [normed_group V₃]
variables (f g : normed_group_hom V₁ V₂)

instance : has_coe_to_fun (normed_group_hom V₁ V₂) := ⟨_, normed_group_hom.to_fun⟩

@[simp] lemma map_zero : f 0 = 0 := f.to_add_monoid_hom.map_zero

@[simp] lemma map_add (x y) : f (x + y) = f x + f y := f.to_add_monoid_hom.map_add _ _

@[simp] lemma map_sub (x y) : f (x - y) = f x - f y := f.to_add_monoid_hom.map_sub _ _

@[simp] lemma map_neg (x) : f (-x) = -(f x) := f.to_add_monoid_hom.map_neg _

lemma bound : ∃ C, 0 < C ∧ ∀ v, ∥f v∥ ≤ C * ∥v∥ :=
begin
  obtain ⟨C, hC⟩ := f.bound',
  use [max C 1],
  simp only [lt_max_iff, zero_lt_one, or_true, true_and],
  intro v,
  calc ∥f v∥
      ≤ C * ∥v∥ : hC v
  ... ≤ max C 1 * ∥v∥ : mul_le_mul (le_max_left _ _) le_rfl (norm_nonneg _) _,
  exact zero_le_one.trans (le_max_right _ _)
end

lemma lipschitz_of_bound (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  lipschitz_with (nnreal.of_real C) f :=
lipschitz_with.of_dist_le' $ λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

theorem antilipschitz_of_bound {K : nnreal} (h : ∀ x, ∥x∥ ≤ K * ∥f x∥) :
  antilipschitz_with K f :=
antilipschitz_with.of_le_mul_dist $
λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

protected lemma uniform_continuous (f : normed_group_hom V₁ V₂) :
  uniform_continuous f :=
begin
  obtain ⟨C, C_pos, hC⟩ := f.bound,
  exact (lipschitz_of_bound f C hC).uniform_continuous
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

/-- The identity as a continuous map. -/
def id : normed_group_hom V V :=
{ bound' := ⟨1, λ v, show ∥v∥ ≤ 1 * ∥v∥, by rw [one_mul]⟩,
  .. add_monoid_hom.id V }

/-- The composition of continuous maps, as a continuous map. -/
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

instance : add_comm_group (normed_group_hom V₁ V₂) :=
by refine_struct
{ .. normed_group_hom.has_add, .. normed_group_hom.has_zero,
  .. normed_group_hom.has_neg, ..normed_group_hom.has_sub };
{ intros, ext, simp [add_assoc, add_comm, add_left_comm] }

@[simp] lemma comp_zero (f : normed_group_hom V₂ V₃) : f.comp (0 : normed_group_hom V₁ V₂) = 0 :=
by { ext, exact f.map_zero' }

@[simp] lemma zero_comp (f : normed_group_hom V₁ V₂) : (0 : normed_group_hom V₂ V₃).comp f = 0 :=
by { ext, refl }

end normed_group_hom

namespace NormedGroup

instance bundled_hom : bundled_hom @normed_group_hom :=
⟨@normed_group_hom.to_fun, @normed_group_hom.id, @normed_group_hom.comp, @normed_group_hom.coe_inj⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] NormedGroup

/-- Construct a bundled `NormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [normed_group M] : NormedGroup := bundled.of M

noncomputable
instance : inhabited NormedGroup := ⟨of punit⟩

instance (M : NormedGroup) : normed_group M := M.str

@[simp] lemma coe_of (R : Type u) [normed_group R] : (NormedGroup.of R : Type u) = R := rfl

instance : limits.has_zero_morphisms.{u (u+1)} NormedGroup :=
{ comp_zero' := by { intros, apply normed_group_hom.zero_comp },
  zero_comp' := by { intros, apply normed_group_hom.comp_zero } }

end NormedGroup
