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
/-
### These are now all in mathlib, I think

lemma abs_smul {α : Type*} [linear_ordered_add_comm_group α] (n : ℕ) (a : α) :
  abs (n • a) = n • abs a := by admit

lemma abs_add_eq_add_abs {α : Type*} [linear_ordered_add_comm_group α]  {a b : α} (hle : a ≤ b) :
  abs (a + b) = abs a + abs b ↔ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) := by admit

lemma abs_add_eq_add_abs_iff {α : Type*} [linear_ordered_add_comm_group α]  (a b : α) :
  abs (a + b) = abs a + abs b ↔ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) := by admit

-/

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

def nonzero_sign : ℤ → ℤ := λ n, if n ≥ 0 then 1 else -1

@[simp] def is_sign : ℤ → Prop
| (1 : ℤ) := true
| (-1 : ℤ) := true
| (n : ℤ) := false

lemma is_sign_sign : ∀ (i : ℤ), is_sign (nonzero_sign i) :=
begin
  intro i,
  by_cases hi : i ≥ 0,
  simp [nonzero_sign, if_pos hi],
  simp [nonzero_sign, if_neg hi],
end

def sign_vectors (ι : Type*) := { ε : ι → ℤ // ∀ i : ι, is_sign (ε i) }

lemma fintype_sign_vectors : fintype ι → fintype (sign_vectors ι) := sorry

end sign_vectors

/--Given a list l of elements of Λ and a functional x, (pos_vector l x) is the sign-vector of
the values of x (l i).
-/
def pos_vector [fintype ι] (l : ι → Λ) (x : Λ →+ ℤ) : sign_vectors ι :=
begin
  let ε_0 := λ i : ι, nonzero_sign (x (l i)),
  have hε : ∀ i, is_sign (ε_0 i),
  { intro i,
    dsimp [ε_0],
    apply is_sign_sign },
  use ⟨ε_0, hε⟩,
end

lemma smul_to_explicit_dual_set [fintype ι] (l : ι → Λ) (x : Λ →+ ℤ) :
  x ∈ (explicit_dual_set ((pos_vector l x).val • l)) :=
begin
  intro,
  dsimp [pos_vector, nonzero_sign],
  by_cases h_pos : x(l i) ≥ 0,
  { rw [if_pos h_pos, one_smul], exact h_pos },
  { rw [if_neg h_pos, neg_smul, one_smul, add_monoid_hom.map_neg, neg_nonneg],
    rw not_le at h_pos,
    exact le_of_lt h_pos },
end

lemma pos_vector_id_if_nonneg [fintype ι] (l : ι → Λ) (x : Λ →+ ℤ) (i : ι) : x (l i) ≥ 0 →
    ((pos_vector l x).val • l) i = l i :=
begin
  intro hx,
  dsimp [pos_vector, nonzero_sign],
  rw [if_pos hx, one_smul],
end

lemma pos_vector_neg_if_neg [fintype ι] (l : ι → Λ) (x : Λ →+ ℤ) (i : ι) : x (l i) < 0 →
    ((pos_vector l x).val • l) i = - l i :=
begin
  intro hx,
  { dsimp [pos_vector, nonzero_sign],
    rw lt_iff_not_ge at hx,
    rw [if_neg hx, neg_smul, one_smul] },
end



/-- Given a list l, a vector of signs ε (and an integer N), (pos_A l ε) is a finite set of functionals satisfying the
requirements of Lemma 9.7 of [Analytic] with respect to all functionals which are positive on all ((ε • l) i)'s.
Its existence is established in lem97_pos.
-/
def pos_A [fintype ι] (hΛ : finite_free Λ) (N : ℕ)
  (l : ι → Λ) (ε : sign_vectors ι) : finset (Λ →+ ℤ) :=
begin
  obtain B := some (lem97_pos hΛ N (ε.1 • l)),
  use B,
end

lemma posA_to_explicit [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (l : ι → Λ) (ε : sign_vectors ι)
  (x' : Λ →+ ℤ) (H : x' ∈ pos_A hΛ N l ε) : x' ∈ explicit_dual_set (ε.1 • l):=
begin
  exact (some_spec (lem97_pos hΛ N (ε.1 • l))).1 x' H,
end

variables [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (l : ι → Λ) (ε : sign_vectors ι)
  (x : Λ →+ ℤ) (H : x ∈ (explicit_dual_set (ε.1 • l)))

lemma exists_good_pair [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (l : ι → Λ) (ε : sign_vectors ι)
  (x : Λ →+ ℤ) (H : x ∈ (explicit_dual_set (ε.1 • l))) : ∃ x' y : (Λ →+ ℤ),
  x' ∈ pos_A hΛ N l ε ∧ x = N • y + x' ∧ ∀ i, x' ((ε.1 • l) i) ≤ x ((ε.1 • l) i) :=
begin
  obtain ⟨x', hx', ⟨y, hy⟩⟩ := (some_spec (lem97_pos hΛ N (ε.1 • l))).2 x H,
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
  let A := finset.bUnion (@finset.univ (sign_vectors ι) (fintype_sign_vectors _)) (pos_A hΛ N l),
  use A,
  intro,
  have hx : x ∈ (explicit_dual_set ((pos_vector l x).1 • l)) := smul_to_explicit_dual_set l x,
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
    have h_pos' : x' ∈ explicit_dual_set ((pos_vector l x).val • l) :=
        by apply posA_to_explicit hΛ N l (pos_vector l x) x' mem_x',
    replace h_pos' : x' (((pos_vector l x).val • l) i) ≥ 0 := by apply h_pos',
    by_cases h_pos : x (l i) ≥ 0,
    { specialize hx' i,
      have h_posvect_id : ((pos_vector l x).val • l) i = l i := pos_vector_id_if_nonneg l x i h_pos,
      replace h_pos' : 0 ≤ x' (l i),
      { rw h_posvect_id at h_pos', exact h_pos' },
      rw h_posvect_id at hx',
      apply or.inl,
      apply and.intro h_pos',
      simp only [sub_nonneg, add_monoid_hom.sub_apply, hx'] },
    { replace h_pos: x (l i) < 0 := by { rw lt_iff_not_ge, exact h_pos },
      specialize hx' i,
      have h_posvect_neg : ((pos_vector l x).val • l) i = - l i := pos_vector_neg_if_neg l x i h_pos,
      replace h_pos' : 0 ≥ x' (l i),
      { rw h_posvect_neg at h_pos',
        simp only [ge_iff_le, add_monoid_hom.map_neg, coe_fn_coe_base, neg_nonneg] at h_pos',
        exact h_pos' },
        rw h_posvect_neg at hx',
        apply or.inr,
        apply and.intro h_pos',
        simp [*] at *, }},
    assumption,
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
