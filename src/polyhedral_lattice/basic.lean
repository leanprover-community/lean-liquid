import analysis.normed_space.basic
import ring_theory.finiteness

noncomputable theory
open_locale big_operators classical nnreal

section move_this

-- rewrite to include multiplicative version
-- also write version for modules, glue to version for groups
def torsion_free (A : Type*) [add_comm_group A] : Prop :=
∀ (a : A) (ha : a ≠ 0) (n : ℕ), n • a = 0 → n = 0

variables {R ι : Type*} [comm_ring R] [fintype ι]
variables (M : ι → Type*) [Π i, add_comm_group (M i)] [Π i, module R (M i)]

-- instance module.finite.pi : module.finite R (Π i, M i) :=
-- sorry

end move_this

section generates_norm

variables {Λ ι : Type*} [normed_group Λ] [fintype ι]

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

class polyhedral_lattice (Λ : Type*) [normed_group Λ] :=
[fg : module.finite ℤ Λ]
(tf : torsion_free Λ)
(polyhedral [] : ∃ (ι : Type) [fintype ι] (x : ι → Λ), generates_norm x)

attribute [instance] polyhedral_lattice.fg
