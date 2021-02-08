import data.real.nnreal
import tactic.ring

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

def res {C : mock_complex} {c c' : ℝ≥0} {i : ℤ} (x : C c' i) (hc : c ≤ c' . magic) : C c i :=
C.restriction c' c i hc x

def d {C : mock_complex} {c : ℝ≥0} {i : ℤ} (x : C c i) : C c (i+1) :=
C.differential c i x

lemma d_res {C : mock_complex} {c c' : ℝ≥0} {i : ℤ} (x : C c' i) (hc : c ≤ c') :
  d (res x) = res (d x) :=
by apply C.commute

lemma res_res {C : mock_complex} {c c' c'' : ℝ≥0} {i : ℤ} (x : C c'' i) (h : c ≤ c') (h' : c' ≤ c'') :
  res (res x) = res x :=
by apply C.restriction_functorial

lemma res_res_mul {C : mock_complex} {c k : ℝ≥0} {i : ℤ} (x : C (k^2*c) i) (h : 1 ≤ k) :
  (res (res x : C (k*c) i) (by magic) : C c i) = res x :=
--  @res C c (k*c) i (res x) (by simp [stupid_one, stupid_two, stupid_three, *]) = res x :=
by apply C.restriction_functorial

-- this doesn't work, because DTT
-- example {C : mock_complex} {c} {i} (x : C c i) : ∃ y : C c (i-1), d y = x := sorry

section
open tactic

meta def magic' : tactic unit :=
do (tactic.interactive.refl <|> assumption <|> tactic.interactive.ring1 none) <|>
   target >>= trace

end

def aux {C : mock_complex} {c : ℝ≥0} {i j : ℤ} (h : j = i) (x : C c i) : C c j :=
h.symm.rec_on x

def d' {C : mock_complex} {c : ℝ≥0} {i j : ℤ} (x : C c i) (hij : j = i + 1 . magic') : C c j :=
aux hij $ C.differential c i x

example {C : mock_complex} {c} {i} (x : C c i) : ∃ y : C c (i-1), d' y = x :=
sorry

lemma d'_res {C : mock_complex} {c c' : ℝ≥0} {i j : ℤ} (x : C c' i) (hc : c ≤ c') (hj : j = i + 1) :
  (d' (res x) : C c j) = res (d' x) :=
by { cases hj, apply C.commute }
