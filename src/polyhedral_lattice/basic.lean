import analysis.normed_space.normed_group_hom
import ring_theory.finiteness
import linear_algebra.free_module
import ring_theory.int.basic

/-!

# Polyhedral lattices

A polyhedral lattice is a finite free ℤ-module with a real-valued norm
making it into a normed group, such that the closed unit ball of
the Banach space obtained by tensoring everything up to ℝ is a rational polyhedron.

## Implementation issues

The condition on the norm actually used is `generates_norm` below.

-/
noncomputable theory
open_locale big_operators classical nnreal

section generates_norm

variables {Λ ι : Type*} [semi_normed_group Λ] [fintype ι]

/-- A finite family `x : ι → Λ` generates the norm on `Λ`
if for every `l : Λ` there exist coefficients `c : ι → ℕ`
such that `l = ∑ i, c i • x i` and `∥l∥ = ∑ i, (c i) * ∥x i∥`.
-/
def generates_norm (x : ι → Λ) :=
∀ l : Λ, ∃ (c : ι → ℕ), (l = ∑ i, c i • x i) ∧ (∥l∥ = ∑ i, c i * ∥x i∥)

lemma generates_norm_iff_generates_nnnorm (x : ι → Λ) :
  generates_norm x ↔
  ∀ l : Λ, ∃ (c : ι → ℕ),
    (l = ∑ i, c i • x i) ∧ (nnnorm l = ∑ i, c i * nnnorm (x i)) :=
begin
  apply forall_congr, intro l,
  simp only [← nnreal.eq_iff, nnreal.coe_mul, nnreal.coe_sum, nnreal.coe_nat_cast, coe_nnnorm]
end

lemma generates_norm.generates_nnnorm {x : ι → Λ} (hl : generates_norm x) :
  ∀ l : Λ, ∃ (c : ι → ℕ), (l = ∑ i, c i • x i) ∧ (nnnorm l = ∑ i, c i * nnnorm (x i)) :=
(generates_norm_iff_generates_nnnorm x).mp hl

lemma generates_norm_of_generates_nnnorm {x : ι → Λ}
  (H : ∀ l : Λ, ∃ (c : ι → ℕ), (l = ∑ i, c i • x i) ∧ (nnnorm l = ∑ i, c i * nnnorm (x i))) :
  generates_norm x :=
(generates_norm_iff_generates_nnnorm x).mpr H

end generates_norm

class polyhedral_lattice (Λ : Type*) extends normed_group Λ :=
[finite [] : module.finite ℤ Λ]
[free   [] : module.free ℤ Λ]
(polyhedral' [] : ∃ (ι : Type) [fintype ι] (l : ι → Λ), generates_norm l)

namespace polyhedral_lattice

variables (Λ : Type*) [polyhedral_lattice Λ]

attribute [instance] polyhedral_lattice.finite polyhedral_lattice.free

instance no_zero_smul_divisors_int : no_zero_smul_divisors ℤ Λ :=
module.free.no_zero_smul_divisors ℤ Λ

instance no_zero_smul_divisors_nat : no_zero_smul_divisors ℕ Λ :=
⟨λ n l h, by { rw [← gsmul_coe_nat, smul_eq_zero] at h,
  refine h.imp _ id, simp only [imp_self, int.coe_nat_eq_zero] }⟩

lemma polyhedral :
  ∃ (ι : Type) [fintype ι] (l : ι → Λ), by exactI generates_norm l ∧ ∀ i, l i ≠ 0 :=
begin
  obtain ⟨ι, _ι_inst, l, hl⟩ := polyhedral_lattice.polyhedral' Λ, resetI,
  refine ⟨{i // l i ≠ 0}, infer_instance, λ i, l i, _, λ i, i.2⟩,
  intro x,
  obtain ⟨c, h1, h2⟩ := hl x,
  refine ⟨λ i, c i, _, _⟩,
  { rw h1,
    refine finset.sum_bij_ne_zero _ (λ _ _ _, finset.mem_univ _) _ _ _,
    { rintro i - hi, refine ⟨i, _⟩, contrapose! hi, rw [hi, smul_zero] },
    { dsimp, rintro i j - hi - hj, simp only [imp_self], },
    { rintro ⟨i, hi⟩ -, dsimp, intro H, refine ⟨i, finset.mem_univ _, H, rfl⟩ },
    { intros, refl } },
  { rw h2,
    refine finset.sum_bij_ne_zero _ (λ _ _ _, finset.mem_univ _) _ _ _,
    { rintro i - hi, refine ⟨i, _⟩, contrapose! hi, rw [hi, norm_zero, mul_zero] },
    { dsimp, rintro i j - hi - hj, simp only [imp_self], },
    { rintro ⟨i, hi⟩ -, dsimp, intro H, refine ⟨i, finset.mem_univ _, H, rfl⟩ },
    { intros, refl } },
end

-- move this
lemma int.div_eq_zero (d n : ℤ) (h : d ∣ n) (H : n / d = 0) : n = 0 :=
by rw [← int.mul_div_cancel' h, H, mul_zero]

end polyhedral_lattice

/-- A morphism of polyhedral lattices is a norm-nonincreasing group homomorphism. -/
structure polyhedral_lattice_hom (Λ₁ Λ₂ : Type*) [polyhedral_lattice Λ₁] [polyhedral_lattice Λ₂] :=
(to_fun : Λ₁ → Λ₂)
(map_add' : ∀ l₁ l₂, to_fun (l₁ + l₂) = to_fun l₁ + to_fun l₂)
(strict' : ∀ l, ∥to_fun l∥ ≤ ∥l∥)

namespace add_monoid_hom

variables {Λ₁ Λ₂ : Type*} [polyhedral_lattice Λ₁] [polyhedral_lattice Λ₂]
variables {f g : polyhedral_lattice_hom Λ₁ Λ₂}

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_polyhedral_lattice_hom'` for a version that uses `ℝ≥0` for the bound. -/
def mk_polyhedral_lattice_hom (f : Λ₁ →+ Λ₂) (h : ∀ v, ∥f v∥ ≤ ∥v∥) :
  polyhedral_lattice_hom Λ₁ Λ₂ :=
{ strict' := h, ..f }

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_polyhedral_lattice_hom` for a version that uses `ℝ` for the bound. -/
def mk_polyhedral_lattice_hom' (f : Λ₁ →+ Λ₂) (h : ∀ x, nnnorm (f x) ≤ nnnorm x) :
  polyhedral_lattice_hom Λ₁ Λ₂ :=
{ strict' := h, .. f}

end add_monoid_hom

namespace polyhedral_lattice_hom

variables {Λ Λ₁ Λ₂ Λ₃ : Type*}
variables [polyhedral_lattice Λ] [polyhedral_lattice Λ₁] [polyhedral_lattice Λ₂] [polyhedral_lattice Λ₃]
variables {f g : polyhedral_lattice_hom Λ₁ Λ₂}

instance : has_coe_to_fun (polyhedral_lattice_hom Λ₁ Λ₂) := ⟨_, polyhedral_lattice_hom.to_fun⟩

initialize_simps_projections polyhedral_lattice_hom (to_fun → apply)

lemma coe_inj (H : ⇑f = g) : f = g :=
by cases f; cases g; congr'; exact funext H

lemma coe_injective : @function.injective (polyhedral_lattice_hom Λ₁ Λ₂) (Λ₁ → Λ₂) coe_fn :=
by apply coe_inj

lemma coe_inj_iff : f = g ↔ ⇑f = g := ⟨congr_arg _, coe_inj⟩

@[ext] lemma ext (H : ∀ x, f x = g x) : f = g := coe_inj $ funext H

lemma ext_iff : f = g ↔ ∀ x, f x = g x := ⟨by rintro rfl x; refl, ext⟩

variables (f g)

@[simp] lemma to_fun_eq_coe : f.to_fun = f := rfl

@[simp] lemma coe_mk (f) (h₁) (h₂) : ⇑(⟨f, h₁, h₂⟩ : polyhedral_lattice_hom Λ₁ Λ₂) = f := rfl

@[simp] lemma coe_mk_polyhedral_lattice_hom (f : Λ₁ →+ Λ₂) (h) :
  ⇑(f.mk_polyhedral_lattice_hom h) = f := rfl

@[simp] lemma coe_mk_polyhedral_lattice_hom' (f : Λ₁ →+ Λ₂) (h) :
  ⇑(f.mk_polyhedral_lattice_hom' h) = f := rfl

/-- The group homomorphism underlying a bounded group homomorphism. -/
def to_add_monoid_hom (f : polyhedral_lattice_hom Λ₁ Λ₂) : Λ₁ →+ Λ₂ :=
add_monoid_hom.mk' f f.map_add'

@[simp] lemma coe_to_add_monoid_hom : ⇑f.to_add_monoid_hom = f := rfl

lemma to_add_monoid_hom_injective :
  function.injective (@polyhedral_lattice_hom.to_add_monoid_hom Λ₁ Λ₂ _ _) :=
λ f g h, coe_inj $ show ⇑f.to_add_monoid_hom = g, by { rw h, refl }

@[simp] lemma mk_to_add_monoid_hom (f) (h₁) (h₂) :
  (⟨f, h₁, h₂⟩ : polyhedral_lattice_hom Λ₁ Λ₂).to_add_monoid_hom = add_monoid_hom.mk' f h₁ := rfl

@[simp] lemma map_zero : f 0 = 0 := f.to_add_monoid_hom.map_zero

@[simp] lemma map_add (x y) : f (x + y) = f x + f y := f.to_add_monoid_hom.map_add _ _

@[simp] lemma map_sum {ι : Type*} (Λ : ι → Λ₁) (s : finset ι) :
  f (∑ i in s, Λ i) = ∑ i in s, f (Λ i) :=
f.to_add_monoid_hom.map_sum _ _

@[simp] lemma map_sub (x y) : f (x - y) = f x - f y := f.to_add_monoid_hom.map_sub _ _

@[simp] lemma map_neg (x) : f (-x) = -(f x) := f.to_add_monoid_hom.map_neg _

@[simp] lemma map_gsmul (n : ℤ) (x) : f (n • x) = n • (f x) := f.to_add_monoid_hom.map_gsmul _ _

instance : has_zero (polyhedral_lattice_hom Λ₁ Λ₂) :=
⟨(0 : Λ₁ →+ Λ₂).mk_polyhedral_lattice_hom (by simp [le_refl])⟩

lemma strict (l : Λ₁) : ∥f l∥ ≤ ∥l∥ := f.strict' l

lemma strict_nnnorm (l : Λ₁) : nnnorm (f l) ≤ nnnorm l := f.strict' l

@[simps]
def to_normed_group_hom : normed_group_hom Λ₁ Λ₂ :=
{ bound' := ⟨1, by simpa only [one_mul] using f.strict⟩, .. f }

/-- The identity as a polyhedral lattice hom. -/
@[simps]
def id : polyhedral_lattice_hom Λ Λ :=
(add_monoid_hom.id Λ).mk_polyhedral_lattice_hom (by simp [le_refl])

/-- The composition of polyhedral lattice homs. -/
@[simps]
protected def comp (g : polyhedral_lattice_hom Λ₂ Λ₃) (f : polyhedral_lattice_hom Λ₁ Λ₂) :
  polyhedral_lattice_hom Λ₁ Λ₃ :=
(g.to_add_monoid_hom.comp f.to_add_monoid_hom).mk_polyhedral_lattice_hom $
  λ l, (g.strict' _).trans (f.strict' _)

end polyhedral_lattice_hom
