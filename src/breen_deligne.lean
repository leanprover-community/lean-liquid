import linear_algebra.matrix
import group_theory.free_abelian_group

/-
Suppose you have an abelian group `A`.
What data do you need to specify a "universal" map `f : ℤ[A^m] → ℤ[A^n]`?
That is, it should be functorial in `A`.

Well, such a map is specified by what it does to `(a 1, a 2, a 3, ..., a m)`.
It can send this element to an arbitrary element of `ℤ[A^n]`,
but it has to be "universal".

In the end, this means that `f` will be a `ℤ`-linear combination of
"basic universal maps", where a "basic universal map" is one that
sends `(a 1, a 2, ..., a m)` to `(b 1, ..., b n)`,
where `b i` is a `ℤ`-linear combination `c i 1 * a 1 + ... + c i m * a m`.
So a "basic universal map" is specified by the `n × m`-matrix `c`.
-/

namespace breen_deligne_data

open_locale big_operators

@[derive add_comm_group]
def basic_universal_map (m n : ℕ) := matrix (fin n) (fin m) ℤ

def basic_universal_map.eval {m n : ℕ} (f : basic_universal_map m n) (A : Type*) [add_comm_group A] :
  free_abelian_group (fin m → A) →+ free_abelian_group (fin n → A) :=
free_abelian_group.lift $ λ a, free_abelian_group.of $ λ i, ∑ j, f i j • a j

@[derive add_comm_group]
def universal_map (m n : ℕ) := finsupp (basic_universal_map m n) ℤ

def universal_map.eval {m n : ℕ} (f : universal_map m n) (A : Type*) [add_comm_group A] :
  free_abelian_group (fin m → A) →+ free_abelian_group (fin n → A) :=
finsupp.sum f $ λ f_basic k, k • f_basic.eval A

end breen_deligne_data
