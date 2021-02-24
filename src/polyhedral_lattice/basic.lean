import analysis.normed_space.basic
import ring_theory.finiteness
import algebra.direct_sum

-- import hacks_and_tricks.by_exactI_hack
-- import hacks_and_tricks.type_pow

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

/-- A finite family `x : ι → Λ` generates the norm on `Λ`
if for every `l : Λ`,
there exists a scaling factor `d : ℕ`, and coefficients `c : ι → ℕ`,
such that `d • l = ∑ i, c i • x i` and `d * ∥l∥ = ∑ i, (c i) * ∥x i∥`.
-/
def generates_norm {Λ ι : Type*} [normed_group Λ] [fintype ι] (x : ι → Λ) :=
∀ l : Λ, ∃ (d : ℕ) (hd : 0 < d) (c : ι → ℕ),
  (d • l = ∑ i, c i • x i) ∧ ((d : ℝ) * ∥l∥ = ∑ i, (c i : ℝ) * ∥x i∥)

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
  tf := sorry,
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
    { rw [hl, finset.smul_sum, ← finset.univ_sigma_univ, finset.sum_sigma],
      apply fintype.sum_congr,
      intro i,
      dsimp,
      simp only [mul_smul, ← finset.smul_sum], sorry },
    sorry
  end }

end polyhedral_lattice

lemma int.norm_coe_units (e : units ℤ) : ∥(e : ℤ)∥ = 1 :=
begin
  obtain (rfl|rfl) := int.units_eq_one_or e;
  simp only [units.coe_neg_one, units.coe_one, norm_neg, norm_one_class.norm_one]
end

--move this
@[simp]
lemma int.units_univ : (finset.univ : finset (units ℤ)) = {1, -1} := rfl

lemma int.sum_units_to_nat_aux : ∀ (n : ℤ), n.to_nat • 1 + -((-n).to_nat • 1) = n
| (0 : ℕ)   := rfl
| (n+1 : ℕ) := show ((n+1) • 1 + -(0 • 1) : ℤ) = _,
begin
  simp only [add_zero, mul_one, int.coe_nat_zero, add_left_inj, algebra.smul_def'', zero_mul,
    int.coe_nat_inj', int.coe_nat_succ, ring_hom.eq_nat_cast, int.nat_cast_eq_coe_nat, neg_zero],
end
| -[1+ n]   :=
begin
  show (0 • 1 + -((n+1) • 1) : ℤ) = _,
  simp only [mul_one, int.coe_nat_zero, algebra.smul_def'', zero_mul, int.coe_nat_succ, zero_add,
    ring_hom.eq_nat_cast, int.nat_cast_eq_coe_nat],
  refl
end

lemma int.sum_units_to_nat (n : ℤ) :
  ∑ (i : units ℤ), int.to_nat (i * n) • (i : ℤ) = n :=
begin
  simp only [int.units_univ],
  -- simp makes no further progress :head bandage: :scream: :shock: :see no evil:
  show (1 * n).to_nat • 1 + (((-1) * n).to_nat • -1 + 0) = n,
  simp only [neg_mul_eq_neg_mul_symm, add_zero, one_mul, smul_neg],
  exact int.sum_units_to_nat_aux n
end

@[simp] lemma int.norm_coe_nat (n : ℕ) : ∥(n : ℤ)∥ = n :=
real.norm_coe_nat _

lemma give_better_name : ∀ (n : ℤ), ∥n∥ = ↑(n.to_nat) + ↑((-n).to_nat)
| (0 : ℕ)   := by simp only [add_zero, norm_zero, int.coe_nat_zero, nat.cast_zero, int.to_nat_zero, neg_zero]
| (n+1 : ℕ) := show ∥(↑(n+1):ℤ)∥ = n+1 + 0, by rw [add_zero, int.norm_coe_nat, nat.cast_succ]
| -[1+ n]   := show ∥-↑(n+1:ℕ)∥ = 0 + (n+1), by rw [zero_add, norm_neg, int.norm_coe_nat, nat.cast_succ]

instance int.polyhedral_lattice : polyhedral_lattice ℤ :=
{ fg := by convert module.finite.self _,
  tf := λ m hm n h,
  begin
    rw [← nsmul_eq_smul, nsmul_eq_mul, mul_eq_zero] at h,
    simpa only [hm, int.coe_nat_eq_zero, or_false, int.nat_cast_eq_coe_nat] using h
  end,
  rational :=
  begin
    intro n, refine ⟨abs n, _⟩,
    simpa only [rat.cast_abs, rat.cast_coe_int] using rfl
  end,
  polyhedral :=
  begin
    refine ⟨units ℤ, infer_instance, coe, _⟩,
    intro n,
    refine ⟨1, zero_lt_one, (λ e, int.to_nat (e * n)), _, _⟩,
    { rw [int.sum_units_to_nat, one_smul] },
    { simp only [int.norm_coe_units, mul_one, nat.cast_one, one_mul, int.units_univ],
      show ∥n∥ = ((1 * n).to_nat) + (↑(((-1) * n).to_nat) + 0),
      simp only [neg_mul_eq_neg_mul_symm, add_zero, one_mul],
      exact give_better_name n }
  end }


