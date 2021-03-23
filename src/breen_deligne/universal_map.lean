import linear_algebra.matrix
import group_theory.free_abelian_group
import algebra.direct_sum
import algebra.big_operators.finsupp

import for_mathlib.linear_algebra

import hacks_and_tricks.type_pow
import hacks_and_tricks.by_exactI_hack

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

local attribute [instance] type_pow
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

/-- A `basic_universal_map m n` is an `n × m`-matrix.
It captures data for a homomorphism `ℤ[A^m] → ℤ[A^n]`
functorial in the abelian group `A`.

A general such homomorphism is a formal linear combination
of `basic_universal_map`s, which we aptly call `universal_map`s. -/
@[derive add_comm_group]
def basic_universal_map (m n : ℕ) := matrix (fin n) (fin m) ℤ

namespace basic_universal_map

variables {k l m n : ℕ} (g : basic_universal_map m n) (f : basic_universal_map l m)
variables (A : Type*) [add_comm_group A]

/-- `f.eval A` for a `f : basic_universal_map m n`
is the homomorphism `ℤ[A^m] →+ ℤ[A^n]` induced by matrix multiplication. -/
def eval : ℤ[A^m] →+ ℤ[A^n] :=
map $ λ x i, ∑ j, g i j • (x : fin _ → A) j

@[simp] lemma eval_of (x : A^m) :
  g.eval A (of x) = (of $ λ i, ∑ j, g i j • x j) :=
lift.of _ _

/-- The composition of basic universal maps,
defined as matrix multiplication. -/
def comp : basic_universal_map l n := matrix.mul g f

lemma eval_comp : (g.comp f).eval A = (g.eval A).comp (f.eval A) :=
begin
  ext1 x,
  simp only [add_monoid_hom.coe_comp, function.comp_app, eval_of, comp, finset.smul_sum,
    matrix.mul_apply, finset.sum_smul, mul_smul],
  congr' 1,
  ext1 i,
  exact finset.sum_comm
end

lemma comp_assoc
  (h : basic_universal_map m n) (g : basic_universal_map l m) (f : basic_universal_map k l) :
  comp (comp h g) f = comp h (comp g f) :=
matrix.mul_assoc _ _ _

/-- The identity `basic_universal_map`. -/
def id (n : ℕ) : basic_universal_map n n := (1 : matrix (fin n) (fin n) ℤ)

@[simp] lemma id_comp : (id _).comp f = f :=
by simp only [comp, id, matrix.one_mul]

@[simp] lemma comp_id : g.comp (id _) = g :=
by simp only [comp, id, matrix.mul_one]

end basic_universal_map

/-- A `universal_map m n` is a formal `ℤ`-linear combination
of `basic_universal_map`s.
It captures the data for a homomorphism `ℤ[A^m] → ℤ[A^n]`. -/
@[derive add_comm_group]
def universal_map (m n : ℕ) := ℤ[basic_universal_map m n]

namespace universal_map
universe variable u

variables {k l m n : ℕ} (g : universal_map m n) (f : universal_map l m)
variables (A : Type u) [add_comm_group A]

/-- `f.eval A` for a `f : universal_map m n`
is the homomorphism `ℤ[A^m] →+ ℤ[A^n]` induced by matrix multiplication
of the summands occurring in the formal linear combination `f`. -/
def eval : universal_map m n →+ ℤ[A^m] →+ ℤ[A^n] :=
free_abelian_group.lift $ λ (f : basic_universal_map m n), f.eval A

@[simp] lemma eval_of (f : basic_universal_map m n) :
  eval A (of f) = f.eval A :=
lift.of _ _

/-- The composition of `universal_map`s `g` and `f`,
given by the formal linear combination of all compositions
of summands occurring in `g` and `f`. -/
def comp : universal_map m n →+ universal_map l m →+ universal_map l n :=
free_abelian_group.lift $ λ (g : basic_universal_map m n), free_abelian_group.lift $ λ f,
of $ g.comp f

@[simp] lemma comp_of (g : basic_universal_map m n) (f : basic_universal_map l m) :
  comp (of g) (of f) = of (g.comp f) :=
by rw [comp, lift.of, lift.of]

section
open add_monoid_hom

lemma eval_comp : eval A (comp g f) = (eval A g).comp (eval A f) :=
show comp_hom (comp_hom (@eval l n A _)) (comp) g f =
  comp_hom (comp_hom (comp_hom.flip (@eval l m A _)) (comp_hom)) (@eval m n A _) g f,
begin
  congr' 2, clear f g, ext g f : 2,
  show eval A (comp (of g) (of f)) = (eval A (of g)).comp (eval A (of f)),
  simp only [basic_universal_map.eval_comp, comp_of, eval_of]
end

lemma comp_assoc (h : universal_map m n) (g : universal_map l m) (f : universal_map k l) :
  comp (comp h g) f = comp h (comp g f) :=
show comp_hom (comp_hom (@comp k l n)) (@comp l m n) h g f =
     comp_hom (comp_hom (comp_hom.flip (@comp k l m)) (comp_hom)) (@comp k m n) h g f,
begin
  congr' 3, clear h g f, ext h g f : 3,
  show comp (comp (of h) (of g)) (of f) = comp (of h) (comp (of g) (of f)),
  simp only [basic_universal_map.comp_assoc, comp_of]
end

/-- The identity `universal_map`. -/
def id (n : ℕ) : universal_map n n := of (basic_universal_map.id n)

@[simp] lemma id_comp : comp (id _) f = f :=
show comp (id _) f = add_monoid_hom.id _ f,
begin
  congr' 1, clear f, ext1 f,
  simp only [id, comp_of, id_apply, basic_universal_map.id_comp]
end

@[simp] lemma comp_id : comp g (id _) = g :=
show (@comp m m n).flip (id _) g = add_monoid_hom.id _ g,
begin
  congr' 1, clear g, ext1 g,
  show comp (of g) (id _) = (of g),
  simp only [id, comp_of, id_apply, basic_universal_map.comp_id]
end

/-- `double f` is the `universal_map` from `ℤ[A^m ⊕ A^m]` to `ℤ[A^n ⊕ A^n]`
given by applying `f` on both "components". -/
def double : universal_map m n →+ universal_map (m + m) (n + n) :=
map $ λ f, matrix.reindex_linear_equiv sum_fin_sum_equiv sum_fin_sum_equiv $
matrix.from_blocks f 0 0 f

lemma double_of (f : basic_universal_map m n) :
  double (of f) =
  of (matrix.reindex_linear_equiv sum_fin_sum_equiv sum_fin_sum_equiv $ matrix.from_blocks f 0 0 f) :=
rfl

lemma comp_double_double (g : universal_map m n) (f : universal_map l m) :
  comp (double g) (double f) = double (comp g f) :=
show comp_hom (comp_hom (comp_hom.flip (@double l m)) ((@comp (l+l) (m+m) (n+n)))) (double) g f =
     comp_hom (comp_hom (@double l n)) (@comp l m n) g f,
begin
  congr' 2, clear g f, ext g f : 2,
  show comp (double (of g)) (double (of f)) = double (comp (of g) (of f)),
  simp only [double_of, comp_of, basic_universal_map.comp],
  rw [matrix.reindex_mul, matrix.from_blocks_multiply],
  congr' 2,
  simp only [add_zero, matrix.zero_mul, zero_add, matrix.mul_zero],
end

lemma double_zero : double (0 : universal_map m n) = 0 :=
double.map_zero

end

end universal_map

end breen_deligne

#lint- only unused_arguments def_lemma doc_blame
