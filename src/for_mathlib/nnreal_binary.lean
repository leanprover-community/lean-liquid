import data.real.nnreal -- non-negative reals
import topology.algebra.infinite_sum -- infinite sums
import analysis.special_functions.log -- just need log
import tactic

open_locale nnreal -- notation for non-negative reals

open_locale big_operators -- notation for infinite sums
/-

move this

-/


lemma stupid_lemma {r : ℝ≥0} (hr : r < 1) : 2 * r < 2 :=
begin
  suffices : 2 * r < 2 * 1, by simpa,
  exact (mul_lt_mul_left (by norm_num)).mpr hr,
end

-- 2 * x < 2 + 2 -> 2 * x - 2 < 2

-- probably true in more generality
lemma nnreal.sub_lt {a b c : ℝ≥0} (hc : c ≠ 0) (h : a < b + c) : a - b < c :=
begin
  cases le_or_lt a b with hab hab,
  { rw tsub_eq_zero_of_le hab,
    exact zero_lt_iff.mpr hc },
  { rwa tsub_lt_iff_left hab.le },
end

/-

# cool is_nat class

-/

class is_nat (r : ℝ≥0) : Prop :=
(spec : ∃ n : ℕ, r = n)

-- Jason says maybe there should be a lift tactic to lift questions
-- about nnreals to nats

namespace is_nat

@[simp] instance zero : is_nat 0 := ⟨⟨0, rfl⟩⟩

end is_nat

class is_pnat (r : ℝ≥0) : Prop :=
(spec : ∃ n : ℕ, r = n + 1)

namespace is_pnat

@[simp] instance one : is_pnat 1 := ⟨⟨0, by simp⟩⟩

lemma one_le {r : ℝ≥0} (hr : is_pnat r) : 1 ≤ r :=
begin
  unfreezingI {obtain ⟨n, rfl⟩ := hr.spec},
  apply self_le_add_left,
end

lemma zero_lt {r : ℝ≥0} (hr : is_pnat r) : 0 < r :=
lt_of_lt_of_le zero_lt_one hr.one_le

lemma pos {r : ℝ≥0} (hr : is_pnat r) : 0 < r := zero_lt hr

end is_pnat

/-

# binary_aux

An auxiliary function which computes the digits and remainders in the binary
expanion of a non-negative real.

-/

-- Is this the fundamental object, or is `binary`?
/-- Auxiliary function which returns binary expansion of `r` if `0 ≤ r < 1`
and junk otherwise. The domain of `binary_aux r` might best be thought of as `pnat`. -/
noncomputable def binary_aux (r : ℝ≥0) : ℕ → (ℕ × (ℝ≥0))
| 0 := (if r < 2⁻¹ then 0 else 1, 2 * r)
| (n + 1) := let digit := if (binary_aux n).2 < 1 then 0 else 1 in
             (digit, 2 * ((binary_aux n).2 - (digit : ℝ≥0)))

namespace binary_aux

/-

would be nice to turn on computable reals mode with same notation

binary_aux 0.15
(0,0.3)
(0,0.6)
(0,1.2)
(1,0.4)
(0,0.8)
(0.1.6)
(1,1.2)
(1,0.4)


-/

variables (r : ℝ≥0) (n : ℕ)

lemma zero_def : binary_aux r 0 = (if r < 2⁻¹ then 0 else 1, 2 * r) :=
binary_aux.equations._eqn_1 r

/-- if 0 ≤ r < 1 then this is the first digit after the decimal point. -/
lemma zero_def_fst : (binary_aux r 0).1 = if r < 2⁻¹ then 0 else 1 := by rw zero_def

-- We decided to store the "remainder term" in the region [0,2) because it made some recursions
-- cleaner
lemma zero_def_snd : (binary_aux r 0).2 = 2 * r := by rw zero_def

lemma succ_def_fst : (binary_aux r (n + 1)).1 = if (binary_aux r n).2 < 1 then 0 else 1 :=
by rw binary_aux.equations._eqn_2

lemma succ_def_snd : (binary_aux r (n + 1)).2 = 2 * ((binary_aux r n).2 - (binary_aux r (n + 1)).1) :=
by rw binary_aux.equations._eqn_2

variable {r}


theorem fst_le_one (r : ℝ≥0) (n : ℕ) : (binary_aux r n).1 ≤ 1 :=
begin
  cases n with d hd,
  { rw zero_def,
    split_ifs; linarith },
  { rw succ_def_fst,
    split_ifs; linarith },
end

lemma two_bdd (hr : r < 1) : (binary_aux r n).2 < 2 :=
begin
  induction n with d hd,
  { simp [zero_def, stupid_lemma hr], },
  { simp only [succ_def_snd, succ_def_fst, nat.cast_ite, nat.cast_zero, nat.cast_one],
    split_ifs with LEM,
    { simp [stupid_lemma LEM] at * },
    { --clear LEM,
    revert hd,
      generalize : (binary_aux r d).snd = x,
      intro hx,
      rw [mul_tsub, mul_one],
      apply nnreal.sub_lt (by norm_num : (2 : ℝ≥0) ≠ 0),
      suffices : 2 * x < 2 * 2, by convert this; norm_num,
      exact (mul_lt_mul_left (by norm_num)).mpr hx }, }
end

-- I think I want an unconditional theorem about `(binary_aux r 0).fst` perhaps under some
-- bounds on r like r < 1

-- still don't have the statement-- need something other than 37
-- lemma def_one : (binary_aux r n).1 = if n = 0 then ite (r < 2⁻¹) 0 1 else 37 ^ n :=
-- begin
--   induction n with d hd,
--   { simp [zero_def_one], },
--   rw succ_def_one,
--   simp,
--   sorry,
-- end

-- def nnreal.tsub_tsub' {a b c : ℝ≥0} (h : c ≤ b) : a - (b - c) = a + c - b :=
-- begin
--   have h1 : b ≤ a + c :
-- end

lemma nnreal.lt_of_sub_pos {a b : ℝ≥0} (h : 0 < a - b) : b < a := tsub_pos_iff_lt.mp h




lemma snd_thing (hr : r < 37) : is_pnat (1 + 2 ^ (n + 1) * r - (binary_aux r n).2) :=
begin
  induction n with d hd, { simp [zero_def_snd], }, -- base case done
  have := hd.one_le,
  --have hpos :=
  have foo : (binary_aux r d).2 ≤ 2 ^ (d + 1) * r,
  { have this2 := hd.pos,
    rw tsub_pos_iff_lt at this2,
    rw le_iff_exists_add,
    rcases hd with ⟨j, hj⟩,
    use j,
    rw tsub_eq_iff_eq_add_of_le this2.le at hj,
    apply add_left_cancel,
    convert hj using 1,
    ring,
  },
  simp [succ_def_snd, succ_def_fst],
  split_ifs,
  sorry; { simp,
    rcases hd with ⟨j, hj⟩,
    use 2 * j,
    apply @add_left_cancel _ _ (1 : ℝ≥0),
    convert_to _ = (2 : ℝ≥0) * (j + 1) using 1, push_cast, ring,
    rw ← hj, clear hj,
    ring_exp,
    rw [tsub_mul, mul_comm (2 : ℝ≥0)],
    rw ← add_tsub_assoc_of_le, swap,
    { --replace foo := mul_le_mul_of_nonneg_right foo _,
      refine le_trans (mul_le_mul_of_nonneg_right foo _) _, norm_num,
      simp [nat.succ_eq_add_one, pow_add],
      rw le_iff_exists_add, use 1,
      ring },
    congr',
    ring_exp },
  { push_neg at h,
    have this2 := hd.pos,
    rw le_iff_exists_add at h,
    generalize hs : (binary_aux r d).snd = s,
    rw hs at *, clear hs,
    rcases h with ⟨c, rfl⟩,
    simp only [add_tsub_cancel_left],
    rw [pow_add, pow_one, nat.succ_eq_add_one],
    rcases hd with ⟨j, hj⟩,
    rw add_tsub_add_eq_tsub_left at hj,
    use 2 * j + 2,
    convert_to _ = (1 : ℝ≥0) + 2 * (j + 1), push_cast, ring,
    rw [← hj, mul_tsub],
    rw ← add_tsub_assoc_of_le, swap,
    { apply mul_le_mul_of_nonneg_left,
      refine le_trans _ foo,
      apply self_le_add_left, norm_num },
    congr' 2,
    ring_exp },
end

#exit
lemma snd_thing (hr : r < 37) : is_nat (2 ^ (n + 1) * r - (binary_aux r n).2) :=
begin
  induction n with d hd,
  { simp [zero_def_snd], },
  { rcases hd with ⟨n, hn⟩,
    simp only [succ_def_snd, succ_def_fst, nat.cast_ite, nat.cast_zero, nat.cast_one],
    split_ifs with h h,
    { use 2 * n,
      push_cast [← hn, tsub_zero, tsub_mul],
      ring_nf,
      rw [mul_tsub],
      congr' 1,
      ring_exp,
    },
    { use 2 * n + 2,
      push_neg at h,
      rw le_iff_exists_add at h,
      rcases h with ⟨s, hs⟩,
      rw hs at hn ⊢,
      push_cast [← hn],
      ring_nf,
      simp [tsub_mul, mul_tsub, mul_add],
      ring_exp,
    sorry }
  }
end


-- what about a formula for 2 in terms of finite sums


-- can't think of a statement which works for fixed r
-- lemma def_two : (binary_aux r n).2 = 2 * (r - ↑⌊r⌋₊) + ∑ i in finset.range n, 37 :=
-- begin
--   induction n with d hd,
--   { simp [zero_def] },
--   { rw succ_def_two,
--     rw finset.sum_range_succ,
--     sorry },
-- end

-- aah maybe I need to be allowed to move `r` too

-- what is relation between binary_aux r and binary_aux (2 * r) or (2⁻¹ * r)?

theorem binary_aux_two_mul : binary_aux (2 * r) n = binary_aux r n.succ :=
begin
  -- I am just going to knock up some experiments
  sorry
end





-- this is somehow the fundamental theorem
theorem binary_aux_finsetsum_bdd (r : ℝ≥0) (hr : r < 1) (B : ℕ) :
  r ∈ set.Ico
  (∑ n in finset.range B, ((binary_aux r n).1 : ℝ≥0) * 2⁻¹ ^ n)
  (2⁻¹ ^ B + ∑ n in finset.range B, (((binary_aux r n).1 : ℝ≥0) * 2⁻¹ ^ n))
  :=
begin
  induction B with d hd, { simp [hr] }, -- base case needs r < 1
  rcases hd with ⟨hd1, hd2⟩,
  split,
  { rw finset.sum_range_succ, clear hd1, -- useless
    induction d with e he generalizing hd2, simp [zero_def, hr],
    sorry },
  { sorry }
  -- inductive hypothesis is not strong enough here
  -- also need statement about ...
  -- I know what I need
end

theorem binary_aux_sum (r : ℝ≥0) (hr : r < 2) : ∑' (n : ℕ), ((binary_aux r n).1 : ℝ≥0) * 2⁻¹ ^ n = r :=
begin
  sorry,
end


#exit

noncomputable def binary (r : ℝ≥0) : ℤ → ℕ := if r = 0 then 0 else
λ n, let d : ℤ := ⌈(r : ℝ).log / (2⁻¹ : ℝ).log⌉ in
if n < d then 0 else binary_aux (n - d).nat_abs
sorry
/-
r > 0; now need biggest d : ℤ such that 2⁻¹ ^ d ≤ r
2^(-d)<=r
(-d) log 2 <= log r
(-d) <= log r / log 2
d >= -log(r)/log(2)=log(r)/(-log(2))=log(r)/log(2⁻¹)
-/

theorem binary_le_one (r : ℝ≥0) (z : ℤ) : binary r z ≤ 1 := sorry

theorem binary_sum (r : ℝ≥0) : ∑' (n : ℤ), (binary r n : ℝ≥0) * 2⁻¹ ^ n = r := sorry
