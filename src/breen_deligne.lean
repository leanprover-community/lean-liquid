import linear_algebra.matrix
import group_theory.free_abelian_group
import algebra.direct_sum

/-!
# Breen-Deligne resolutions

Reference:
https://www.math.uni-bonn.de/people/scholze/Condensed.pdf#section*.4
("Appendix to Lecture IV", p. 28)

-/
noncomputable theory

-- get some notation working:
open_locale big_operators direct_sum
local notation A `^` n := fin n → A
local notation `ℤ[` A `]` := free_abelian_group A

namespace breen_deligne_data

/-!
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

@[derive add_comm_group]
def basic_universal_map (m n : ℕ) := matrix (fin n) (fin m) ℤ

namespace basic_universal_map

variables {l m n : ℕ} (g : basic_universal_map m n) (f : basic_universal_map l m)
variables (A : Type*) [add_comm_group A]

def eval : ℤ[A^m] →+ ℤ[A^n] :=
free_abelian_group.lift $ λ a, free_abelian_group.of $ λ i, ∑ j, g i j • a j

def comp : basic_universal_map l n := matrix.mul g f

lemma eval_comp : (g.comp f).eval A = (g.eval A).comp (f.eval A) :=
begin
  -- we need an `ext` lemma for homs out of `free_abelian_group`s.
  sorry
end

end basic_universal_map

@[derive add_comm_group]
def universal_map (m n : ℕ) := finsupp (basic_universal_map m n) ℤ

namespace universal_map

variables {l m n : ℕ} (g : universal_map m n) (f : universal_map l m)
variables (A : Type*) [add_comm_group A]

def eval : ℤ[A^m] →+ ℤ[A^n] := finsupp.sum g $ λ g_basic k, k • g_basic.eval A

def comp : universal_map l n := finsupp.sum g $ λ g_basic k,
                                finsupp.sum f $ λ f_basic k',
                                (finsupp.single (g_basic.comp f_basic) (k * k'))

lemma eval_comp : (g.comp f).eval A = (g.eval A).comp (f.eval A) :=
begin
  sorry
end

end universal_map

/-!
In the end, we want a complex of maps `⊕_i ℤ[A^i] → ⊕_j ℤ[A^j]`.
-/

@[derive add_comm_group]
def termwise_data {m n : ℕ} (k : ℕ^m) (l : ℕ^n) := Π i j, universal_map (k i) (l j)

namespace termwise_data

def eval {m n : ℕ} {k : ℕ^m} {l : ℕ^n} (f : termwise_data k l) (A : Type*) [add_comm_group A] :
  (⨁ i, ℤ[A^(k i)]) →+ ⨁ j, ℤ[A^(l j)] :=
direct_sum.to_add_monoid $ λ i, sorry -- fail, we don't know how to do maps into direct sums

variables {l m n : ℕ} {x : ℕ^l} {y : ℕ^m} {z : ℕ^n}
variables (g : termwise_data y z) (f : termwise_data x y)
variables (A : Type*) [add_comm_group A]

include g f -- ← can be removed once the def is actually filled in
def comp : termwise_data x z := sorry

lemma eval_comp : (g.comp f).eval A = (g.eval A).comp (f.eval A) :=
begin
  sorry
end

end termwise_data

end breen_deligne_data

structure breen_deligne_data :=
(nr_of_summands : ℕ → ℕ)
(ranks : Π n, ℕ^(nr_of_summands n))
(data  : Π n, breen_deligne_data.termwise_data (ranks (n+1)) (ranks n))

namespace breen_deligne_data

variables (BD : breen_deligne_data)

def is_complex : Prop := ∀ n, (BD.data n).comp (BD.data (n+1)) = 0

end breen_deligne_data

theorem breen_deligne : ∃ BD : breen_deligne_data, BD.is_complex := sorry
