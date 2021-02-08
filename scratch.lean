import data.real.nnreal
import tactic.gptf

open_locale nnreal

structure mock_complex :=
(obj : ℝ≥0 → ℤ → Type)
(differential : ∀ c i, obj c i → obj c (i+1))
(restriction : ∀ c' c i, c ≤ c' → obj c' i → obj c i)
(restriction_functorial : ∀ c c' c'' i (h : c ≤ c') (h' : c' ≤ c'') (x : obj c'' i),
  restriction c' c i h (restriction c'' c' i h' x) = restriction c'' c i (h.trans h') x)
(commute : ∀ c c' i (h : c ≤ c') (x : obj c' i),
  differential c i (restriction c' c i h x) = restriction c' c (i+1) h (differential c' i x))

instance : has_coe_to_fun mock_complex :=
⟨λ C, ℝ≥0 → ℤ → Type, λ C, C.obj⟩

section
open tactic

example {c c' c'' : ℝ≥0} (h : c ≤ c') (h' : c' ≤ c'') : c ≤ c'' :=
begin
  rw ← nnreal.coe_le_coe at *,
  linarith,
end

lemma stupid_one {c k : ℝ≥0} (h : 1 ≤ k) : c ≤ k*c:=
begin
  conv_lhs { rw ← one_mul c },
  exact mul_le_mul_right' h c
end

lemma stupid_two {c k : ℝ≥0} (h : 1 ≤ k) : c ≤ k^2*c:=
begin
  rw [pow_two, mul_assoc],
  have : c ≤ k*c := stupid_one h,
  conv_lhs { rw ← one_mul c },
  apply mul_le_mul ; try { assumption } ; exact nnreal.zero_le_coe
end

lemma stupid_three {c k : ℝ≥0} (h : 1 ≤ k) : k*c ≤ k^2*c:=
begin
  rw [pow_two, mul_assoc],
  exact stupid_one h,
end

meta def magic : tactic unit :=
do (assumption >> trace "by assumption" <|>
   `[rw ← nnreal.coe_le_coe at *, linarith] >> trace "by linarith") <|>
   `[simp [stupid_one, stupid_two, stupid_three, *]] <|>
   target >>= trace

end

def res {C : mock_complex} (c c' : ℝ≥0) {i : ℤ} (x : C c' i) (hc : c ≤ c' . magic) : C c i :=
C.restriction c' c i hc x

def d {C : mock_complex} {c : ℝ≥0} {i : ℤ} (x : C c i) : C c (i+1) :=
C.differential c i x

lemma d_res {C : mock_complex} {c c' : ℝ≥0} {i : ℤ} (x : C c' i) (hc : c ≤ c') :
  d (res _ _ x) = res _ _ (d x) :=
by apply C.commute

lemma res_res {C : mock_complex} {c c' c'' : ℝ≥0} {i : ℤ} (x : C c'' i) (h : c ≤ c') (h' : c' ≤ c'') :
  res _ _ (res _ _ x) = res _ _ x :=
by apply C.restriction_functorial

lemma res_res_mul {C : mock_complex} {c k : ℝ≥0} {i : ℤ} (x : C (k^2*c) i) (h : 1 ≤ k) :
  res c (k*c) (res (k*c) (k^2*c) x) = res _ _ x :=
--  @res C c (k*c) i (res x) (by simp [stupid_one, stupid_two, stupid_three, *]) = res x :=
by apply C.restriction_functorial
