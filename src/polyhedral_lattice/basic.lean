import analysis.normed_space.normed_group_hom
import ring_theory.finiteness
import data.int.basic
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

-- no longer necessary after big mathlib refactor?
local attribute [-instance] add_comm_group.int_module

section move_this

-- rewrite to include multiplicative version
-- also write version for modules, glue to version for groups
def torsion_free (A : Type*) [add_comm_group A] : Prop :=
∀ (a : A) (ha : a ≠ 0) (n : ℕ), n • a = 0 → n = 0

-- TODO: remove [semimodule ℤ A]
-- TODO: multiplicative version once this is removed
-- TODO: `is_basis` is being bundled by Anne so there's no point filling in proofs right now :-/

/-- `finite_free M` is the statement that the abelian group `M` is free of finite rank (over `ℤ`).-/
def finite_free (A : Type*) [add_comm_group A] [semimodule ℤ A] : Prop :=
∃ (ι : Type) [fintype ι] (x : ι → A), is_basis ℤ x

namespace finite_free

variables {A : Type*} [add_comm_group A] [semimodule ℤ A] (ha : finite_free A)

/-- If `ha : finite_free Λ` then `ha.basis_type` is the `ι` which indexes the basis
  `ha.basis : ι → Λ`. -/
def basis_type : Type := classical.some ha

instance : fintype (basis_type ha) := classical.some $ classical.some_spec ha

/-- If `ha : finite_free Λ` then `ha.basis : ι → Λ` is the basis. Here `ι := ha.basis_type`. -/
def basis : ha.basis_type → A := classical.some $ classical.some_spec $ classical.some_spec ha

theorem is_basis : is_basis ℤ ha.basis :=
classical.some_spec $ classical.some_spec $ classical.some_spec ha

theorem top_fg (ha : finite_free A) : (⊤ : submodule ℕ A).fg :=
begin
  use (finset.image (ha.basis) finset.univ) ∪ (finset.image (-ha.basis) finset.univ),
  rw eq_top_iff,
  rintro a -,
  have hA := ha.is_basis,
  rw ← hA.total_repr a,
  generalize : (hA.repr) a = f, clear a,
  apply finsupp.induction f; clear f,
  { exact submodule.zero_mem _ },
  { intros i z f hif hz hf,
    rw linear_map.map_add,
    refine submodule.add_mem _ _ hf,
    simp only [set.image_univ, finset.coe_union, pi.neg_apply, finsupp.total_single, linear_map.to_add_monoid_hom_coe,
      finset.coe_univ, finset.coe_image],
    -- next 6 lines -- what am I missing? I rewrite this twice later.
    have should_be_easy : ∀ (n : ℕ) (b : A), (n : ℤ) • b = n • b,
    { intros,
      induction n with n hn,
        simp,
      rw [nat.succ_eq_add_one, add_smul, ←hn],
      simp [add_smul] },
    let n := z.nat_abs,
    by_cases hz2 : z ≤ 0,
    -- nearly there
    { -- messy z≤0 case
      have hn2 : (n : ℤ) = - z := int.of_nat_nat_abs_of_nonpos hz2,
      rw [eq_neg_iff_eq_neg, ← mul_neg_one] at hn2,
      rw [hn2, mul_smul, neg_one_smul, should_be_easy],
      refine submodule.smul_mem _ n (submodule.subset_span (or.inr ⟨i, rfl⟩)) },
    { push_neg at hz2,
      rw [← int.of_nat_nat_abs_eq_of_nonneg (le_of_lt hz2)],
      change (n : ℤ) • _ ∈ _,
      rw should_be_easy,
      refine submodule.smul_mem _ n (submodule.subset_span (or.inl ⟨i, rfl⟩)) } },
end

theorem dual (ha : finite_free A) : finite_free (A →+ ℤ) :=
begin
  -- do this after is_basis refactor?
  sorry
end

/-- The rank of a finite free abelian group. -/
def rank (ha : finite_free A) : ℕ := fintype.card ha.basis_type

variable {ha}

/-- A rank zero abelian group has at most one element (yeah I know...). -/
lemma rank_zero (h0 : ha.rank = 0) : subsingleton A := subsingleton.intro
begin
  -- do this after is_basis refactor?
  sorry
end


end finite_free

end move_this

section generates_norm

variables {Λ ι : Type*} [semi_normed_group Λ] [fintype ι]

/-- A finite family `x : ι → Λ` generates the norm on `Λ`
if for every `l : Λ`,
there exists a scaling factor `d : ℕ`, and coefficients `c : ι → ℕ`,
such that `d • l = ∑ i, c i • x i` and `d * ∥l∥ = ∑ i, (c i) * ∥x i∥`.
-/
def generates_norm (x : ι → Λ) :=
∀ l : Λ, ∃ (d : ℕ) (hd : 0 < d) (c : ι → ℕ),
  (d • l = ∑ i, c i • x i) ∧ ((d : ℝ) * ∥l∥ = ∑ i, (c i : ℝ) * ∥x i∥)

lemma generates_norm_iff_generates_nnnorm (x : ι → Λ) :
  generates_norm x ↔
  ∀ l : Λ, ∃ (d : ℕ) (hd : 0 < d) (c : ι → ℕ),
    (d • l = ∑ i, c i • x i) ∧ ((d : ℝ≥0) * nnnorm l = ∑ i, (c i : ℝ≥0) * nnnorm (x i)) :=
begin
  apply forall_congr, intro l,
  simp only [← nnreal.eq_iff, nnreal.coe_mul, nnreal.coe_sum, nnreal.coe_nat_cast, coe_nnnorm]
end

lemma generates_norm.generates_nnnorm {x : ι → Λ} (hl : generates_norm x) :
  ∀ l : Λ, ∃ (d : ℕ) (hd : 0 < d) (c : ι → ℕ),
    (d • l = ∑ i, c i • x i) ∧ ((d : ℝ≥0) * nnnorm l = ∑ i, (c i : ℝ≥0) * nnnorm (x i)) :=
(generates_norm_iff_generates_nnnorm x).mp hl

lemma generates_norm_of_generates_nnnorm {x : ι → Λ}
  (H : ∀ l : Λ, ∃ (d : ℕ) (hd : 0 < d) (c : ι → ℕ),
    (d • l = ∑ i, c i • x i) ∧ ((d : ℝ≥0) * nnnorm l = ∑ i, (c i : ℝ≥0) * nnnorm (x i))) :
  generates_norm x :=
(generates_norm_iff_generates_nnnorm x).mpr H

end generates_norm

class polyhedral_lattice (Λ : Type*) extends semi_normed_group Λ :=
-- unfortunately, we need the following assumptions, for technical reasons
[int_semimodule : semimodule ℤ Λ]
[is_scalar_tower : is_scalar_tower ℕ ℤ Λ]
-- now we get to the actual definition
(finite_free : finite_free Λ)
(polyhedral [] : ∃ (ι : Type) [fintype ι] (l : ι → Λ),
  generates_norm l ∧ ∀ i, nnnorm (l i) ≠ 0)
  -- this final condition ↑ ↑ ↑ ↑ effectively means that we have a `normed_group`
  -- but this condition is easier to check when forming quotients

attribute [instance] polyhedral_lattice.int_semimodule
                     polyhedral_lattice.is_scalar_tower

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
