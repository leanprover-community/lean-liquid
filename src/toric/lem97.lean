import algebra.group.basic
import analysis.convex.cone
import linear_algebra.dual

import polyhedral_lattice.basic
import toric.is_inj_nonneg
-- import toric.pairing_dual_saturated -- fae: I have commented this `import`, it gives an error


section move

variables [α  : Type*] [add_comm_group α]
theorem nat.neg_smul (k : ℕ) (x : α) : - (k : ℤ) • x = - (k • x) :=
eq_neg_of_add_eq_zero (by rw [← nsmul_eq_smul, ← gsmul_coe_nat, gsmul_eq_smul,
  ← add_smul, add_left_neg, zero_smul])

lemma nat.self_sub_mod_div (n k : ℕ) : n = n % k + k * ((n - n %k)/k) :=
by rw [mul_comm, nat.div_mul_cancel (nat.dvd_sub_mod n), ← nat.add_sub_assoc (nat.mod_le n k),
    add_comm, nat.add_sub_cancel]

end move

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


lemma explicit_dual_set_of_neg (l : ι → Λ) (x : Λ →+ ℤ) :
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

lemma lem97_pos (hΛ : finite_free Λ) [fintype ι] (N : ℕ) (hN : 0 < N) (l : ι → Λ) :
  ∃ B : finset (Λ →+ ℤ), (∀ b ∈ B, b ∈ (explicit_dual_set l)) ∧
   ∀ x : Λ →+ ℤ, x ∈ (explicit_dual_set l) → ∃ (x' ∈ B) (y : Λ →+ ℤ),
   x = N • y + x' ∧ ∀ i, x' (l i) ≤ x (l i) :=
begin
  obtain ⟨S₀, hS₀⟩ := explicit_gordan hΛ l,
  let S:= { x // x ∈ S₀},
  let Y := S → (fin N),
  let ψ := (λ y : Y, ∑ s in finset.attach S₀, (y s).1 • s.val),--modification?
  let B := finset.image ψ finset.univ,
  use B,
  split,
  { intros b hb,
    rw finset.mem_image at hb,
    rcases hb with ⟨y, ⟨hy₁, h_yb⟩⟩,
    dsimp [ψ] at h_yb,
    rw [← hS₀, ← h_yb],
    apply mem_span_finset.mpr,
    let φ := λ x : (Λ →+ ℤ), if H: x ∈ S₀ then (y ⟨x, H⟩ : ℕ) else 0,
    use φ,
    dsimp [φ],
    rw ← finset.sum_attach,
    apply finset.sum_congr,
    { tauto },
    intros s hs,
    simp only [dite_eq_ite, if_true, finset.coe_mem, finset.mk_coe] },
  { intros x hx,
    rw [← hS₀, mem_span_finset] at hx,
    rcases hx with ⟨f, hx⟩,
    let g : (Λ →+ ℤ) → (fin N) := (λ i, ⟨f i % N, nat.mod_lt (f i) hN⟩),
    obtain ⟨r, hr⟩ : ∃ (r : (Λ →+ ℤ) → ℕ), f = ↑g + N • r,
    { set r := λ x, (f x - g x) / N with hr,
      use r,
      funext z,
      dsimp [g],
      simp only [*, algebra.id.smul_eq_mul, pi.add_apply, eq_self_iff_true, pi.smul_apply],
      exact nat.self_sub_mod_div (f z) N },
    set x' := ∑ (i : Λ →+ ℤ) in S₀, (g i).val • i with hx',
    have H : x' ∈ B,
    { rw finset.mem_image,
      dsimp [ψ],
      rw hx',
      use g ∘ val,
      apply and.intro (finset.mem_univ _),
      let g₁ := λ i, (g i).val • i,
      change' (∑ (s : {x // x ∈ S₀}) in S₀.attach, (f ↑s % N) • ↑s) =
        (∑ (i : Λ →+ ℤ) in S₀, g₁ i),
      conv_rhs {rw [← finset.sum_attach] }},
    let y := ∑ (i : Λ →+ ℤ) in S₀, r i • i,
    use [x', H, y],
    split,
    { ext s,
      rw [← hx, hr],
      dsimp [y, x'],
      rw [finset.smul_sum, ← finset.sum_add_distrib],
      simp_rw [← smul_assoc, ← add_smul, add_comm],
      rw finset.sum_congr,
      refl,
      intros z hz,
      refl },
    intro i,
    dsimp [x'],
    rw [← hx, sub_nonpos.symm, sub_eq_add_neg, ← add_monoid_hom.neg_apply, ← finset.sum_neg_distrib,
      add_monoid_hom.finset_sum_apply, add_monoid_hom.finset_sum_apply, ← finset.sum_add_distrib],
    simp_rw [← add_monoid_hom.add_apply, ← nat.neg_smul, ← nsmul_eq_smul, ← gsmul_coe_nat,
      gsmul_eq_smul, ← add_smul],
    apply finset.sum_nonpos,
    intros z hz,
    replace hz : z ∈ explicit_dual_set l,
    { rw [← submodule.span_singleton_le_iff_mem, ← hS₀],
      apply submodule.span_mono,
      exact set.singleton_subset_iff.mpr hz },
    replace hz : 0 ≤ z (l i) := rfl.mpr hz i,
    rw [add_monoid_hom.int_smul_apply, ← gsmul_eq_smul, gsmul_eq_mul],
    apply mul_nonpos_of_nonpos_of_nonneg _ hz,
    simp only [add_zero, int.cast_id, int.coe_nat_mod, add_neg_le_iff_le_add'],
    rw [← int.coe_nat_mod, int.coe_nat_le_coe_nat_iff],
    apply nat.mod_le },
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

/-- Given a list l, a vector of signs ε (and a positive integer N), (pos_A l ε) is a finite set of functionals satisfying the
requirements of Lemma 9.7 of [Analytic] with respect to all functionals which are positive on all ((ε • l) i)'s.
Its existence is established in lem97_pos.
-/
def pos_A [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (hN : 0 < N)
  (l : ι → Λ) (ε : sign_vectors ι) : finset (Λ →+ ℤ) :=
begin
  obtain B := some (lem97_pos hΛ N hN (ε • l)),
  use B,
end

lemma posA_to_explicit [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (hN : 0 < N)
  (l : ι → Λ) (ε : sign_vectors ι) (x' : Λ →+ ℤ) (H : x' ∈ pos_A hΛ N hN l ε) : x' ∈ explicit_dual_set (ε • l)
  := (some_spec (lem97_pos hΛ N hN (ε • l))).1 x' H


lemma exists_good_pair [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (hN : 0 < N) (l : ι → Λ) (ε : sign_vectors ι)
  (x : Λ →+ ℤ) (H : x ∈ (explicit_dual_set (ε • l))) : ∃ x' y : (Λ →+ ℤ),
  x' ∈ pos_A hΛ N hN l ε ∧ x = N • y + x' ∧ ∀ i, x' ((ε • l) i) ≤ x ((ε • l) i) :=
begin
  obtain ⟨x', hx', ⟨y, hy⟩⟩ := (some_spec (lem97_pos hΛ N hN (ε • l))).2 x H,
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
lemma lem97 [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (hN : 0 <N) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (0 ≤ x' (l i) ∧ 0 ≤ (x - x') (l i)) ∨ (x' (l i) ≤ 0 ∧ (x - x') (l i) ≤ 0) :=
begin
  let A := finset.bUnion (@finset.univ (sign_vectors ι) (fintype_sign_vectors)) (pos_A hΛ N hN l),
  use A,
  intro,
  have hx : x ∈ (explicit_dual_set ((pos_vector l x) • l)) := smul_to_explicit_dual_set l x,
  obtain ⟨x', y, mem_x', hy, hx'⟩ := exists_good_pair hΛ N hN l (pos_vector l x) x hx,
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
        by apply posA_to_explicit hΛ N hN l (pos_vector l x) x' mem_x',
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
lemma lem97' [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (hN : 0 <N) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (x (l i)).nat_abs = N * (y (l i)).nat_abs + (x' (l i)).nat_abs :=
begin
  obtain ⟨A, hA⟩ := lem97 hΛ N hN l,
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
