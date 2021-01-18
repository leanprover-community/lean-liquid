namespace int
/-! ### extend from nat

A helper function to define a function on the integers
by extending a function from the naturals.

We use this to define a complex indexed by `ℤ` by extending a complex indexed by `ℕ`
with zeros on negative indices.
-/

variables {X : ℤ → Sort*} (x : Π i, X i) (f : Π i : ℕ, X i)

def extend_from_nat : Π i, X i
| (n : ℕ)   := f n
| i@-[1+n]  := x i

@[simp] lemma extend_from_nat_apply_nat (n : ℕ) :
  extend_from_nat x f n = f n := rfl

@[simp] lemma extend_from_nat_apply_of_nat (n : ℕ) :
  extend_from_nat x f (int.of_nat n) = f n := rfl

@[simp] lemma extend_from_nat_apply_nat_add_one (n : ℕ) :
  extend_from_nat x f (n+1) = f (n+1) := rfl

@[simp] lemma extend_from_nat_apply_neg_succ_of_nat (n : ℕ) :
  extend_from_nat x f -[1+n] = x -[1+n] := rfl

end int
