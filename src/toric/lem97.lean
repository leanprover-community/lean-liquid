import algebra.group.basic
import analysis.convex.cone
import linear_algebra.dual

import polyhedral_lattice.basic
import toric.is_inj_nonneg
import toric.pairing_dual_saturated

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
  x ∈ (explicit_dual_set (- l)) ↔ ∀ i, x (l i) ≤ 0 :=
begin
  simp_rw [← neg_nonneg, ← add_monoid_hom.map_neg],
  exact iff.rfl,
end

lemma explicit_gordan (hΛ : finite_free Λ) [fintype ι] (l : ι → Λ) :
  (explicit_dual_set l).fg :=
sorry

lemma aux_1 {N : ℕ} {l : ι → Λ} {S₀ : finset (Λ →+ ℤ)}
  (hS₀ : submodule.span ℕ ↑S₀ = explicit_dual_set l) :
  let
      ψ : ({x // x ∈ S₀} → fin N) → Λ →+ ℤ :=
        λ (y : {x // x ∈ S₀} → fin N), ∑ (s : {x // x ∈ S₀}) in S₀.attach, (y s).val • s.val,
      B : finset (Λ →+ ℤ) := finset.image ψ finset.univ
  in ∀ (b : Λ →+ ℤ), b ∈ B → b ∈ explicit_dual_set l :=
begin
  intros ψ B b hb,
  rcases finset.mem_image.mp hb with ⟨y, ⟨hy₁, rfl⟩⟩,
  rw [← hS₀],
  apply mem_span_finset.mpr,
  let φ := λ x : (Λ →+ ℤ), if H: x ∈ S₀ then (y ⟨x, H⟩ : ℕ) else 0,
  use φ,
  rw ← finset.sum_attach,
  refine finset.sum_congr rfl (λ s hs, _),
  simp only [*, dif_pos, dite_eq_ite, val_eq_coe, if_true, finset.coe_mem, finset.mk_coe]
end

lemma aux_2 {N : ℕ} (hN : 0 < N) {l : ι → Λ} {S₀ : finset (Λ →+ ℤ)}
  (hS₀ : submodule.span ℕ ↑S₀ = explicit_dual_set l)
  (f r : (Λ →+ ℤ) → ℕ) :
  let S : Type u_1 := {x // x ∈ S₀},
      Y : Type u_1 := S → fin N,
      ψ : Y → Λ →+ ℤ :=
        λ (y : Y),
          ∑ (s : {x // x ∈ S₀}) in S₀.attach, (y s).val • s.val,
      B : finset (Λ →+ ℤ) := finset.image ψ finset.univ,
      g : (Λ →+ ℤ) → fin N := λ (i : Λ →+ ℤ), ⟨f i % N, nat.mod_lt _ hN⟩,
      x' : Λ →+ ℤ := ∑ (i : Λ →+ ℤ) in S₀, (g i).val • i
  in f = ↑g + N • r →
     x' = ∑ (i : Λ →+ ℤ) in S₀, (g i).val • i →
     x' ∈ B →
     ∀ (i : ι),
       x' (l i) ≤ (⇑∑ (i : Λ →+ ℤ) in S₀, f i • i) (l i) :=
begin
  intros S Y ψ B g x' hr hx' H i,
  dsimp [x'],
  rw [sub_nonpos.symm, sub_eq_add_neg, ← add_monoid_hom.neg_apply, ← finset.sum_neg_distrib,
    add_monoid_hom.finset_sum_apply, add_monoid_hom.finset_sum_apply, ← finset.sum_add_distrib],
  simp_rw [← add_monoid_hom.add_apply, ← nsmul_eq_smul, ← gsmul_coe_nat, ← neg_gsmul,
    gsmul_eq_smul, ← add_smul],
  apply finset.sum_nonpos,
  intros z hz,
  replace hz : z ∈ explicit_dual_set l,
  { rw [← submodule.span_singleton_le_iff_mem, ← hS₀],
    exact submodule.span_mono (set.singleton_subset_iff.mpr hz) },
  replace hz : 0 ≤ z (l i) := rfl.mpr hz i,
  rw [add_monoid_hom.int_smul_apply, ← gsmul_eq_smul, gsmul_eq_mul],
  apply mul_nonpos_of_nonpos_of_nonneg _ hz,
  simp only [add_zero, int.cast_id, int.coe_nat_mod, add_neg_le_iff_le_add'],
  rw [← int.coe_nat_mod, int.coe_nat_le_coe_nat_iff],
  exact nat.mod_le _ _
end

lemma aux_3 {Λ ι : Type*} (N : ℕ) [add_comm_group Λ] (hN : 0 < N) (l : ι → Λ)
  (S₀ : finset (Λ →+ ℤ)) (hS₀ : submodule.span ℕ ↑S₀ = explicit_dual_set l) :
  let Y : Type u_1 := {x // x ∈ S₀} → fin N,
      ψ : Y → Λ →+ ℤ :=
        λ (y : Y),
          ∑ (s : {x // x ∈ S₀}) in S₀.attach, (y s).val • s.val,
      B : finset (Λ →+ ℤ) := finset.image ψ finset.univ
  in ∀ (x : Λ →+ ℤ),
       x ∈ explicit_dual_set l →
       (∃ (x' : Λ →+ ℤ) (H : x' ∈ B) (y : Λ →+ ℤ),
          x = N • y + x' ∧ ∀ (i : ι), x' (l i) ≤ x (l i)) :=
begin
  intros Y ψ B x hx,
  rw [← hS₀, mem_span_finset] at hx,
  rcases hx with ⟨f, rfl⟩,
  let g : (Λ →+ ℤ) → (fin N) := (λ i, ⟨f i % N, nat.mod_lt (f i) hN⟩),
  obtain ⟨r, hr⟩ : ∃ (r : (Λ →+ ℤ) → ℕ), f = ↑g + N • r,
  { use λ x, (f x - g x) / N,
    refine funext (λ z, (_ : f z = g z + N * ((f z - f z % N) / N))),
    rw [nat.mul_div_cancel' (nat.dvd_sub_mod _)],
    exact (nat.add_sub_cancel' (nat.mod_le _ _)).symm },
  set x' := ∑ (i : Λ →+ ℤ) in S₀, (g i).val • i with hx',
  have H : x' ∈ B,
  { refine finset.mem_image.mpr ⟨g ∘ val, finset.mem_univ _, _⟩,
    convert finset.sum_attach,
    refl },
  refine ⟨x', _, ∑ (i : Λ →+ ℤ) in S₀, r i • i, _, _⟩,
  { refine finset.mem_image.mpr ⟨g ∘ val, finset.mem_univ _, _⟩,
    convert finset.sum_attach,
    refl },
  { rw [hr, finset.smul_sum, ← finset.sum_add_distrib],
    simp_rw [← smul_assoc, ← add_smul, add_comm (N • _) _],
    refl },
  exact aux_2 hN hS₀ (λ i, f i) r hr hx' H,
end

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
  { exact aux_1 hS₀ },
  { refine aux_3 N hN l S₀ hS₀ },
end

section sign_vectors

def nonzero_sign : ℤ → units ℤ := λ n, if 0 ≤ n then 1 else -1

def sign_vectors (ι : Type*) := (ι → units ℤ)

instance sign_vectors_inhabited : inhabited (sign_vectors ι) := ⟨(λ i, 1)⟩

def fintype_sign_vectors [fintype ι] : fintype (sign_vectors ι) := pi.fintype

/--Given a list l of elements of Λ and a functional x, (pos_vector l x) is the sign-vector of
the values of x (l i).
-/
def pos_vector (l : ι → Λ) (x : Λ →+ ℤ) : sign_vectors ι :=
λ i, nonzero_sign (x (l i))

def coe_to_signs : (sign_vectors ι) → (ι → ℤ) :=
λ x i, x i

instance coe_signs : has_coe (sign_vectors ι) (ι → ℤ) := ⟨ coe_to_signs ⟩

instance smul_signs : has_scalar (sign_vectors ι) (ι → Λ) :=
{smul := λ ε l i, (ε i : ℤ) • l i }

lemma smul_to_explicit_dual_set (l : ι → Λ) (x : Λ →+ ℤ) :
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

lemma pos_vector_id_if_nonneg (l : ι → Λ) (x : Λ →+ ℤ) (i : ι) : 0 ≤ x (l i) →
    (pos_vector l x • l) i = l i :=
begin
  intro hx,
  simp only [pos_vector, nonzero_sign, has_scalar.smul, id.def],
  rw [if_pos hx, units.coe_one, one_gsmul],
end

lemma pos_vector_neg_if_neg (l : ι → Λ) (x : Λ →+ ℤ) (i : ι) : x (l i) < 0 →
    ((pos_vector l x) • l) i = - l i :=
begin
  intro hx,
  simp only [pos_vector, nonzero_sign, has_scalar.smul, id.def],
  rw [if_neg (not_le.mpr hx), units.coe_neg, units.coe_one, neg_gsmul, one_gsmul],
end


end sign_vectors

/-- Given a list l, a vector of signs ε (and a positive integer N), (pos_A l ε) is a finite set of functionals satisfying the
requirements of Lemma 9.7 of [Analytic] with respect to all functionals which are positive on all ((ε • l) i)'s.
Its existence is established in lem97_pos.
-/
def pos_A [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (hN : 0 < N)
  (l : ι → Λ) (ε : sign_vectors ι) : finset (Λ →+ ℤ) :=
some (lem97_pos hΛ N hN (ε • l))

lemma posA_to_explicit [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (hN : 0 < N)
  (l : ι → Λ) (ε : sign_vectors ι) (x' : Λ →+ ℤ) (H : x' ∈ pos_A hΛ N hN l ε) : x' ∈ explicit_dual_set (ε • l)
  := (some_spec (lem97_pos hΛ N hN (ε • l))).1 x' H


lemma exists_good_pair [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (hN : 0 < N) (l : ι → Λ) (ε : sign_vectors ι)
  (x : Λ →+ ℤ) (H : x ∈ (explicit_dual_set (ε • l))) : ∃ x' y : (Λ →+ ℤ),
  x' ∈ pos_A hΛ N hN l ε ∧ x = N • y + x' ∧ ∀ i, x' ((ε • l) i) ≤ x ((ε • l) i) :=
begin
  obtain ⟨x', hx', ⟨y, hy⟩⟩ := (some_spec (lem97_pos hΛ N hN (ε • l))).2 x H,
  exact ⟨x', y, hx', hy⟩,
end

/-
jmc: I don't know exactly which version of the two lemmas below
will be easier to prove, `lem97` or `lem97'`.
The first one is closer to [Analytic], but the second one is easier to use.
Mathematically they are indistinguishable.
fae: I am going for the first, `lem97`. I left `lem97'` there, at any rate.
-/


/-- Lemma 9.7 of [Analytic]. -/
lemma lem97 [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (hN : 0 < N) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (0 ≤ x' (l i) ∧ 0 ≤ (x - x') (l i)) ∨ (x' (l i) ≤ 0 ∧ (x - x') (l i) ≤ 0) :=
begin
  refine ⟨(@finset.univ (sign_vectors ι) (fintype_sign_vectors)).bUnion (pos_A hΛ N hN l), λ x, _⟩,
  have hx : x ∈ (explicit_dual_set ((pos_vector l x) • l)) := smul_to_explicit_dual_set l x,
  obtain ⟨x', y, mem_x', hy, hx'⟩ := exists_good_pair hΛ N hN l (pos_vector l x) x hx,
  refine ⟨x', _, _⟩,
  { refine finset.mem_bUnion.mpr ⟨pos_vector l x, _, mem_x'⟩,
    simp only [finset.mem_univ] },
  { refine ⟨y, hy, λ i, _⟩,
    have h_pos' : x' ∈ explicit_dual_set ((pos_vector l x) • l) :=
      posA_to_explicit hΛ N hN l (pos_vector l x) x' mem_x',
    replace h_pos' : 0 ≤ x' (((pos_vector l x) • l) i) := h_pos' _,
    by_cases h_pos : 0 ≤ x (l i),
    {
      have h_posvect_id : ((pos_vector l x) • l) i = l i := pos_vector_id_if_nonneg l x i h_pos,
      replace h_pos' : 0 ≤ x' (l i) := h_pos'.trans (le_of_eq (congr_arg x' h_posvect_id)),
      refine or.inl ⟨h_pos', _⟩,
      rw ← h_posvect_id,
      simp only [sub_nonneg, add_monoid_hom.sub_apply, hx'] },
    { specialize hx' i,
      have h_posvect_neg : ((pos_vector l x) • l) i = - l i :=
        pos_vector_neg_if_neg l x i (not_le.mp h_pos),
      replace h_pos' : 0 ≥ x' (l i),
      { rw [h_posvect_neg, x'.map_neg] at h_pos',
        exact neg_nonneg.mp h_pos' },
      rw h_posvect_neg at hx',
      refine or.inr ⟨h_pos', _⟩,
      simpa only [neg_le_neg_iff, add_monoid_hom.sub_apply, add_monoid_hom.map_neg, sub_nonpos]
        using hx' } }
end
#lint

/-- Lemma 9.7 of [Analytic]. -/
lemma lem97' [fintype ι] (hΛ : finite_free Λ) (N : ℕ) (hN : 0 < N) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (x (l i)).nat_abs = N * (y (l i)).nat_abs + (x' (l i)).nat_abs :=
begin
  obtain ⟨A, hA⟩ := lem97 hΛ N hN l,
  refine ⟨A, λ x, _⟩,
  rcases hA x with ⟨x', mem_x', y, rfl, hx'⟩,
  refine ⟨x', mem_x', y, rfl, λ i, _⟩,
  specialize hx' i,
  convert (abs_add_eq_add_abs_iff _ x').mpr _,
  change abs ((N • y + x') (l i)) = abs (N * (y (l i))) + abs (x' (l i)),
  rw abs_add_eq_add_abs_iff,
  use [x', mem_x', y, hy],
  intro i,
  specialize hx' i,
  zify,
  simp only [← int.abs_eq_nat_abs, hy, add_monoid_hom.add_apply, add_monoid_hom.nat_smul_apply],
  convert_to abs (N • y (l i) + x' (l i)) = abs (N • y (l i)) + abs (x' (l i)) using 2,
  { rw [← nsmul_eq_smul, nsmul_eq_mul, int.nat_cast_eq_coe_nat, abs_mul, int.coe_nat_abs], },
  apply (abs_add_eq_add_abs_iff (N • y (l i)) (x' (l i))).mpr,
  rw [← sub_eq_iff_eq_add] at hy,
  simpa only [hy, add_monoid_hom.nat_smul_apply, and_comm] using hx',
end
