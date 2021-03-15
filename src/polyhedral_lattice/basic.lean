import analysis.normed_space.basic
import ring_theory.finiteness
import linear_algebra.direct_sum_module
import algebra.direct_sum

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
(rational : ∀ l : Λ, ∃ q : ℚ, ∥l∥ = q)
(polyhedral [] : ∃ (ι : Type) [fintype ι] (x : ι → Λ), generates_norm x)

namespace polyhedral_lattice

attribute [instance] polyhedral_lattice.fg

variables {ι : Type} [fintype ι] (Λ : ι → Type*)
variables [Π i, normed_group (Λ i)] [Π i, polyhedral_lattice (Λ i)]

open_locale direct_sum big_operators

instance : has_norm (⨁ i, Λ i) :=
⟨λ x, ∑ i, ∥x i∥⟩

lemma direct_sum_norm_def (x : ⨁ i, Λ i) : ∥x∥ = ∑ i, ∥x i∥ := rfl

instance : normed_group (⨁ i, Λ i) :=
normed_group.of_core _ $
{ norm_eq_zero_iff :=
  begin
    intros x,
    simp only [direct_sum_norm_def, ← coe_nnnorm, ← nnreal.coe_sum, finset.mem_univ,
      nnreal.coe_eq_zero, finset.sum_eq_zero_iff, nnnorm_eq_zero, forall_prop_of_true],
    split,
    { intro h, ext, rw direct_sum.zero_apply, apply h, },
    { rintro rfl, intro, rw direct_sum.zero_apply, }
  end,
  triangle :=
  begin
    intros x y,
    simp only [direct_sum_norm_def, ← finset.sum_add_distrib, direct_sum.add_apply],
    apply finset.sum_le_sum,
    rintro i -,
    apply norm_add_le,
  end,
  norm_neg :=
  begin
    intro x,
    simp only [direct_sum_norm_def],
    apply finset.sum_congr rfl,
    rintro i -,
    rw ← norm_neg (x i),
    congr' 1,
    apply dfinsupp.neg_apply -- this is missing for direct_sum
  end }

instance : polyhedral_lattice (⨁ i, Λ i) :=
{ fg := sorry,
  tf :=
  begin
    intros v hv n hnv,
    obtain ⟨i, nzv_i⟩ : ∃ (i : ι), direct_sum.component ℤ ι Λ i v ≠ 0,
    { rw ← not_forall,
      rwa [ne.def, direct_sum.ext_iff ℤ] at hv },
    have tf_i : torsion_free (Λ i),
    { suffices pl_i : polyhedral_lattice (Λ i),
      exact pl_i.tf,
      apply_assumption },
    refine tf_i (direct_sum.component ℤ ι Λ i v) nzv_i n _,
    rw ← linear_map.map_smul_of_tower,
    convert (direct_sum.ext_iff ℤ).mp hnv i,
  end,
  rational :=
  begin
    intro l,
    have := λ i, polyhedral_lattice.rational (l i),
    choose q hq using this,
    use ∑ i, q i,
    simp only [direct_sum_norm_def, hq],
    change ∑ i, algebra_map ℚ ℝ (q i) = algebra_map ℚ ℝ (∑ i, q i),
    rw ring_hom.map_sum,
  end,
  polyhedral :=
  begin
    have := λ i, polyhedral_lattice.polyhedral (Λ i),
    choose J _instJ x hx using this, resetI,
    refine ⟨Σ i, J i, infer_instance, λ j, direct_sum.of _ j.1 (x _ j.2), _⟩,
    intro l,
    have := λ i, hx i (l i),
    choose d hd c H1 H2 using this,
    let d' : ι → ℕ := λ i₀, ∏ i in (finset.univ.erase i₀), d i,
    have hl : l = ∑ i, direct_sum.of _ i (l i),
    { sorry },
    refine ⟨∏ i, d i, _, λ j, d' j.1 * c j.1 j.2, _, _⟩,
    sorry,
    { rw [hl], -- the weirdness hese is not really clear to me: it works as a simple `rw`
               -- without the linear_algebra.direct_sum_module import.
    have : (∏ (i : ι), d i) • ∑ (i : ι), (direct_sum.of (λ (i : ι), Λ i) i) (l i) =
        ∑ (x : ι), (∏ (i : ι), d i) • (direct_sum.of (λ (i : ι), Λ i) x) (l x) :=
        finset.smul_sum,
    convert this.trans _,
    rw[ ← finset.univ_sigma_univ, finset.sum_sigma],
      apply fintype.sum_congr,
      intro i,
      dsimp,
      sorry }, --simp only [mul_smul, ← finset.smul_sum] },
    sorry
  end }

end polyhedral_lattice
