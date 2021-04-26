import breen_deligne.suitable

noncomputable theory

open_locale nnreal big_operators

namespace breen_deligne

namespace data

variables (BD : data) (r r' : ℝ≥0)

lemma b_exists [hr : fact (r < 1)] (x : ℝ≥0) [fact (0 < x)] :
  ∃ b : ℕ, r ^ b ≤ x⁻¹ :=
begin
  suffices : ∃ b : ℕ, (r ^ b : ℝ) < x⁻¹,
  { rcases this with ⟨b, hb⟩,
    refine ⟨b, le_of_lt _⟩,
    rwa [← nnreal.coe_lt_coe, nnreal.coe_pow, nnreal.coe_inv] },
  refine exists_pow_lt_of_lt_one _ hr.out,
  simp only [nnreal.coe_pos, inv_pos],
  apply fact.out
end

def b [hr : fact (r < 1)] (x : ℝ≥0) [fact (0 < x)] := nat.find (b_exists r x)

/-- Example of a very suitable sequence of constants for given Breen--Deligne data. -/
noncomputable def c_ (BD : data) (r r' : ℝ≥0) [hr : fact (r < 1)] : ℕ → ℝ≥0
| 0     := 1
| (n+1) := ((BD.d (n+1) n).factor)⁻¹ * (r' ^ (b r $ max 1 (BD.d (n+1) n).bound) * c_ n)

instance c_very_suitable [hr : fact (r < 1)] : BD.very_suitable r r' (BD.c_ r r') :=
very_suitable.of_succ _ _ _ _
begin
  intro n,
  let N := max 1 (BD.d (n+1) n).bound,
  let b : ℕ := b r (max 1 (BD.d (n+1) n).bound),
  let c : ℝ≥0 := (BD.d (n+1) n).factor,
  refine ⟨N, b, c * BD.c_ r r' (n+1), le_max_right _ _, _, _, _⟩,
  { intros g hg i,
    refine mul_le_mul' (universal_map.le_factor _ _ hg _) le_rfl },
  { rw [mul_comm, nnreal.mul_le_iff_le_inv, mul_one],
    convert nat.find_spec (b_exists r (max 1 (BD.d (n+1) n).bound)),
    { dsimp [N, max], simp only [eq_self_iff_true, nat.cast_one, nat.cast_ite, nat.cast_le_one],
      congr },
    { apply ne_of_gt,
      simp only [lt_max_iff, nat.cast_max, nat.cast_one, nat.cast_pos, zero_lt_one, true_or], } },
  { by_cases hc : c = 0,
    { simp only [hc, zero_mul, zero_le'] },
    rw nnreal.mul_le_iff_le_inv hc,
    dsimp [c_], exact le_rfl }
end

end data

namespace package

variables (BD : package) (r r' : ℝ≥0)

/-- Example of an adept sequence of constants for
a given Breen--Deligne package `BD` and constants `c_`. -/
def c' (BD : package) (c_ : ℕ → ℝ≥0) : ℕ → ℝ≥0
| 0     := 1
| (n+1) := (BD.homotopy.h n (n + 1)).factor * rescale_constants c_ 2 n * (c_ (n + 1))⁻¹

/-
=== There's a mistake here. jmc knows how to fix it.
-/

lemma c'_monotone (c_ : ℕ → ℝ≥0) : monotone (c' BD c_) :=
sorry -- is this provable?? We might need to tweak the defn a bit

instance c'_adept (c_ : ℕ → ℝ≥0) [BD.data.suitable c_] : -- [∀ i, fact (0 < c_ i)] :
  package.adept BD c_ (c' BD c_) :=
{ one_le := sorry,
  suitable :=
  begin
    constructor,
    intros i j,
    by_cases hij : i = j + 1,
    swap, { rw BD.data.d_eq_zero; [apply_instance, exact hij] },
    subst i,
    have aux1 : BD.c' c_ j ≤ BD.c' c_ (j+1) := c'_monotone BD c_ (nat.le_succ j),
    -- have aux2 := universal_map.factor_le_of_suitable (c_ (j+1)) (c_ j) (BD.data.d (j+1) j),
    apply universal_map.suitable_of_factor_le,
    dsimp,
    sorry, -- now use monotonicity
  end,
  htpy_suitable' :=
  begin
    intros n,
    apply universal_map.suitable_of_factor_le,
    dsimp [c'],
    rw [inv_mul_cancel_right', mul_inv_cancel_right'],
    { dsimp [rescale_constants], sorry },
    { sorry }
  end }

end package

end breen_deligne
