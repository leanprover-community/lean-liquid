import algebra.group.basic
import analysis.convex.cone
import linear_algebra.dual

import polyhedral_lattice.basic
import toric.is_inj_nonneg
-- import toric.pairing_dual_saturated -- fae: I have commented this `import`, it gives an error


/-!
In this file we state and prove 9.7 of [Analytic].
-/

open_locale nnreal big_operators

variables {Λ : Type*} [add_comm_group Λ]
variable {ι : Type*}

noncomputable theory

open classical subtype function embedding

local attribute [instance] prop_decidable


def explicit_dual_set (l : ι → Λ) : submodule ℕ (Λ →+ ℤ) :=
{ carrier := {x | ∀ i, 0 ≤ x (l i)},
  zero_mem' := λ i, le_rfl,
  add_mem' := λ x y hx hy i, add_nonneg (hx i) (hy i),
  smul_mem' := λ n x hx i, by { rw [add_monoid_hom.nat_smul_apply], exact nsmul_nonneg (hx i) n } }


lemma explicit_dual_set_of_neg (l : ι → Λ) (x : Λ →+ℤ) :
  x ∈ (explicit_dual_set (- l)) ↔ ∀ i, 0 ≥ x (l i) :=
begin
  split,
  { intros hx i,
    rw [ge_iff_le, ← neg_nonneg, ← add_monoid_hom.map_neg],
    tauto, },
  { intros hx i,
    erw [add_monoid_hom.map_neg, neg_nonneg, ← ge_iff_le],
    tauto },
end

lemma explicit_gordan (hΛ : finite_free Λ) [fintype ι] (l : ι → Λ) :
  (explicit_dual_set l).fg :=
sorry

lemma lem97_pos (hΛ : finite_free Λ) [fintype ι] (N : ℕ) (l : ι → Λ) :
  ∃ B : finset (Λ →+ ℤ),
    (∀ b ∈ B, b ∈ (explicit_dual_set l)) ∧
    ∀ x : Λ →+ ℤ, x ∈ (explicit_dual_set l) → ∃ (x' ∈ B) (y : Λ →+ ℤ),
      x = N • y + x' ∧ ∀ i, x' (l i) ≤ x (l i) :=
begin
  obtain ⟨S, hS⟩ := explicit_gordan hΛ l,
  use S,--this is wrong, I am just testing the first statement
  split,
  { intros b hb,
    rw ← hS,
    apply submodule.subset_span,
    exact hb },
  { intros x hx,
    sorry },
end

section sign_vectors

def nonzero_sign : ℤ → units ℤ := λ n, if n ≥ 0 then 1 else -1

def sign_vectors (ι : Type*) := (ι → units ℤ)

lemma fintype_sign_vectors [fintype ι] : fintype (sign_vectors ι) := pi.fintype


/--Given a list l of elements of Λ and a functional x, (pos_vector l x) is the sign-vector of
the values of x (l i).
-/
def pos_vector [fintype ι] (l : ι → Λ) (x : Λ →+ ℤ) : sign_vectors ι :=
begin
  intro i,
  use nonzero_sign (x (l i)),
end

def coe_to_signs : (sign_vectors ι) → (ι → ℤ) :=
begin
  intros x i,
  use x i,
end

instance coe_signs : has_coe (sign_vectors ι) (ι → ℤ) := ⟨ coe_to_signs ⟩

instance smul_signs : has_scalar (sign_vectors ι) (ι → Λ) :=
{smul := λ ε l i, (ε i : ℤ) • l i }

lemma smul_to_explicit_dual_set [fintype ι] (l : ι → Λ) (x : Λ →+ ℤ) :
  x ∈ (explicit_dual_set ((pos_vector l x) • l)) :=
begin
  intro j,
  simp only [pos_vector, nonzero_sign, has_scalar.smul, id.def,
    ge_iff_le, add_monoid_hom.map_gsmul, gsmul_int_int],
  by_cases h_pos : x(l j) ≥ 0,
  { rwa [if_pos h_pos, units.coe_one, one_mul], },
  { rw [if_neg h_pos, units.coe_neg, units.coe_one, neg_mul_eq_neg_mul_symm,
      one_mul, neg_nonneg],
    rw not_le at h_pos,
    exact le_of_lt h_pos },
end

lemma pos_vector_id_if_nonneg [fintype ι] (l : ι → Λ) (x : Λ →+ ℤ) (i : ι) : x (l i) ≥ 0 →
    (pos_vector l x • l) i = l i :=
begin
  intro hx,
  simp only [pos_vector, nonzero_sign, has_scalar.smul, id.def, ge_iff_le],
  rw [if_pos hx, units.coe_one, one_gsmul],
end

lemma pos_vector_neg_if_neg [fintype ι] (l : ι → Λ) (x : Λ →+ ℤ) (i : ι) : x (l i) < 0 →
    ((pos_vector l x) • l) i = - l i :=
begin
  intro hx,
  simp only [pos_vector, nonzero_sign, has_scalar.smul, id.def, ge_iff_le],
  dsimp [pos_vector, nonzero_sign],
  rw lt_iff_not_ge at hx,
  rw [if_neg hx, units.coe_neg, units.coe_one, neg_gsmul, one_gsmul],
end


end sign_vectors

/-- Given a list l, a vector of signs ε (and an integer N), (pos_A l ε) is a finite set of functionals satisfying the
requirements of Lemma 9.7 of [Analytic] with respect to all functionals which are positive on all ((ε • l) i)'s.
Its existence is established in lem97_pos.
-/
def pos_A [fintype ι] (hΛ : finite_free Λ) (N : ℕ)
  (l : ι → Λ) (ε : sign_vectors ι) : finset (Λ →+ ℤ) :=
begin
  obtain B := some (lem97_pos hΛ N (ε • l)),
  use B,
end

lemma posA_to_explicit [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (l : ι → Λ) (ε : sign_vectors ι)
  (x' : Λ →+ ℤ) (H : x' ∈ pos_A hΛ N l ε) : x' ∈ explicit_dual_set (ε • l):= (some_spec (lem97_pos hΛ N (ε • l))).1 x' H


lemma exists_good_pair [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (l : ι → Λ) (ε : sign_vectors ι)
  (x : Λ →+ ℤ) (H : x ∈ (explicit_dual_set (ε • l))) : ∃ x' y : (Λ →+ ℤ),
  x' ∈ pos_A hΛ N l ε ∧ x = N • y + x' ∧ ∀ i, x' ((ε • l) i) ≤ x ((ε • l) i) :=
begin
  obtain ⟨x', hx', ⟨y, hy⟩⟩ := (some_spec (lem97_pos hΛ N (ε • l))).2 x H,
  use [x', y],
  exact ⟨hx', hy⟩,
end

/-
jmc: I don't know exactly which version of the two lemmas below
will be easier to prove, `lem97` or `lem97'`.
The first one is closer to [Analytic], but the second one is easier to use.
Mathematically they are indistinguishable.
fae: I am going for the first, `lem97`. I left `lem97'` there, at any rate.
-/


/-- Lemma 9.7 of [Analytic]. -/
lemma lem97 [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (0 ≤ x' (l i) ∧ 0 ≤ (x - x') (l i)) ∨ (x' (l i) ≤ 0 ∧ (x - x') (l i) ≤ 0) :=
begin
  let A := finset.bUnion (@finset.univ (sign_vectors ι) (fintype_sign_vectors)) (pos_A hΛ N l),
  use A,
  intro,
  have hx : x ∈ (explicit_dual_set ((pos_vector l x) • l)) := smul_to_explicit_dual_set l x,
  obtain ⟨x', y, mem_x', hy, hx'⟩ := exists_good_pair hΛ N l (pos_vector l x) x hx,
  use x',
  split,
  { apply finset.mem_bUnion.mpr,
    use (pos_vector l x),
    split,
    simp only [true_and, finset.mem_univ],
    exact mem_x', },
  {  use y,
    apply and.intro hy,
    intro,
    have h_pos' : x' ∈ explicit_dual_set ((pos_vector l x) • l) :=
        by apply posA_to_explicit hΛ N l (pos_vector l x) x' mem_x',
    replace h_pos' : x' (((pos_vector l x) • l) i) ≥ 0 := by apply h_pos',
    by_cases h_pos : x (l i) ≥ 0,
    { specialize hx' i,
      have h_posvect_id : ((pos_vector l x) • l) i = l i := pos_vector_id_if_nonneg l x i h_pos,
      replace h_pos' : 0 ≤ x' (l i),
      { rw h_posvect_id at h_pos', exact h_pos' },
      rw h_posvect_id at hx',
      apply or.inl,
      apply and.intro h_pos',
      simp only [sub_nonneg, add_monoid_hom.sub_apply, hx'] },
    { replace h_pos: x (l i) < 0 := by { rw lt_iff_not_ge, exact h_pos },
      specialize hx' i,
      have h_posvect_neg : ((pos_vector l x) • l) i = - l i := pos_vector_neg_if_neg l x i h_pos,
      replace h_pos' : 0 ≥ x' (l i),
      { rw h_posvect_neg at h_pos',
        simp only [ge_iff_le, add_monoid_hom.map_neg, coe_fn_coe_base, neg_nonneg] at h_pos',
        exact h_pos' },
        rw h_posvect_neg at hx',
        apply or.inr,
        apply and.intro h_pos',
        simp [*] at *, }},
end


/-- Lemma 9.7 of [Analytic]. -/
lemma lem97' [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (x (l i)).nat_abs = N * (y (l i)).nat_abs + (x' (l i)).nat_abs :=
begin
  obtain ⟨A, hA⟩ := lem97 hΛ N l,
  use A,
  intro x,
  specialize hA x,
  rcases hA with ⟨x', mem_x', y, hy, hx'⟩,
  use [x', mem_x', y],
  apply and.intro hy,
  intro i,
  specialize hx' i,
  zify,
  rw [← int.abs_eq_nat_abs, ← int.abs_eq_nat_abs, ← int.abs_eq_nat_abs,
    ← int.coe_nat_abs, ← gsmul_int_int, ← abs_gsmul, gsmul_int_int, ← smul_eq_mul],
  simp only [*, gsmul_int_int, add_sub_cancel,
    add_monoid_hom.add_apply, add_monoid_hom.nat_smul_apply],
  convert_to abs (N • y (l i) + x' (l i)) = abs (N • y (l i)) + abs (x' (l i)),
  { rw [add_left_inj, smul_eq_mul, ← nsmul_eq_smul, nsmul_eq_mul,
    int.nat_cast_eq_coe_nat] },
  { apply (abs_add_eq_add_abs_iff (N • y (l i)) (x' (l i))).mpr,
    rw [hy, add_sub_cancel, add_monoid_hom.nat_smul_apply] at hx',
    cases hx',
    {apply or.inl (and.intro hx'.2 hx'.1) },
    {apply or.inr (and.intro hx'.2 hx'.1) } },
end
