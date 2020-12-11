import linear_algebra.matrix
import group_theory.free_abelian_group
import algebra.direct_sum
import algebra.big_operators.finsupp
import data.tuple

/-!
# Breen-Deligne resolutions

Reference:
https://www.math.uni-bonn.de/people/scholze/Condensed.pdf#section*.4
("Appendix to Lecture IV", p. 28)

We formalize the notion of `breen_deligne_data`.
Roughly speaking, this is a collection of formal finite sums of matrices
that encode that data that rolls out of the Breen--Deligne resolution.

-/
noncomputable theory

-- get some notation working:
open_locale big_operators direct_sum
local notation A `^` n := tuple A n
local notation `ℤ[` A `]` := free_abelian_group A

namespace breen_deligne
open free_abelian_group

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
map $ λ x i, ∑ j, g i j • x j

@[simp] lemma eval_of (x : A^m) :
  g.eval A (of x) = (of $ λ i, ∑ j, g i j • x j) :=
lift.of _ _

def comp : basic_universal_map l n := matrix.mul g f

lemma eval_comp : (g.comp f).eval A = (g.eval A).comp (f.eval A) :=
begin
  ext1 x',
  apply lift.ext,
  intro x,
  simp only [add_monoid_hom.coe_comp, function.comp_app, eval_of, comp, finset.smul_sum,
    matrix.mul_apply, finset.sum_smul, mul_smul],
  congr' 1,
  ext1 i,
  exact finset.sum_comm
end

end basic_universal_map

@[derive add_comm_group]
def universal_map (m n : ℕ) := ℤ[basic_universal_map m n]

namespace universal_map
universe variable u

variables {l m n : ℕ} (g : universal_map m n) (f : universal_map l m)
variables (A : Type u) [add_comm_group A]

def eval : universal_map m n →+ ℤ[A^m] →+ ℤ[A^n] :=
free_abelian_group.lift $ λ f, f.eval A

@[simp] lemma eval_of (f : basic_universal_map m n) :
  eval A (of f) = f.eval A :=
lift.of _ _

def comp : universal_map m n →+ universal_map l m →+ universal_map l n :=
free_abelian_group.lift $ λ g, free_abelian_group.lift $ λ f,
of $ g.comp f

@[simp] lemma comp_of (g : basic_universal_map m n) (f : basic_universal_map l m) :
  comp (of g) (of f) = of (g.comp f) :=
lift.of _ _

section
open add_monoid_hom

lemma eval_comp : eval A (comp g f) = (eval A g).comp (eval A f) :=
show comp_hom (comp_hom (@eval l n A _)) (comp) g f =
  comp_hom (comp_hom (comp_hom.flip (@eval l m A _)) (comp_hom)) (@eval m n A _) g f,
begin
  congr' 1, apply lift.ext; clear g; intro g,
  ext1 f; apply lift.ext; clear f; intro f,
  show eval A (comp (of g) (of f)) = (eval A (of g)).comp (eval A (of f)),
  simp only [basic_universal_map.eval_comp, comp_of, eval_of]
end

-- we probably want some `finvec` goodies to make this look better
def double : universal_map m n →+ universal_map (m + m) (n + n) :=
map $ λ f, tuple.append
(λ j, tuple.append (f j) 0)
(λ j, tuple.append 0 (f j))

end

end universal_map

/-- Roughly speaking, this is a collection of formal finite sums of matrices
that encode that data that rolls out of the Breen--Deligne resolution. -/
structure data :=
(rank       : ℕ → ℕ)
(map        : Π n, universal_map (rank (n+1)) (rank n))
(rank_zero  : rank 0 = 1) -- this "hardcodes" that the complex end in `ℤ[A] → A`
(is_complex : ∀ n, universal_map.comp (map n) (map (n+1)) = 0)

-- we probably want some `finvec` goodies to make this more pleasant.
def σ_add (BD : data) (n : ℕ) : universal_map (BD.rank n + BD.rank n) (BD.rank n) :=
of $ λ j, tuple.append (λ i, if i = j then 1 else 0) (λ i, if i = j then 1 else 0)

def σ_proj (BD : data) (n : ℕ) : universal_map (BD.rank n + BD.rank n) (BD.rank n) :=
of (λ j, tuple.append (λ i, if i = j then 1 else 0) 0) +
of (λ j, tuple.append 0 (λ i, if i = j then 1 else 0))

structure homotopy (BD : data) :=
(map         : Π n, universal_map (BD.rank n + BD.rank n) (BD.rank (n+1)))
(is_homotopy : ∀ n, σ_add BD (n+1) - σ_proj BD (n+1) =
                universal_map.comp (BD.map (n+1)) (map (n+1)) +
                universal_map.comp (map n) (BD.map n).double)
(is_homotopy_zero : σ_add BD 0 - σ_proj BD 0 = sorry) -- do we want/need this?

end breen_deligne
