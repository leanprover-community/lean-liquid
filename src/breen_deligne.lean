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

@[derive add_comm_group]
def basic_universal_map (m n : ℕ) := matrix (fin n) (fin m) ℤ

namespace basic_universal_map

variables {k l m n : ℕ} (g : basic_universal_map m n) (f : basic_universal_map l m)
variables (A : Type*) [add_comm_group A]

def eval : ℤ[A^m] →+ ℤ[A^n] :=
map $ λ x i, ∑ j, g i j • (x : fin _ → A) j

@[simp] lemma eval_of (x : A^m) :
  g.eval A (of x) = (of $ λ i, ∑ j, g i j • x j) :=
lift.of _ _

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

def id (n : ℕ) : basic_universal_map n n := (1 : matrix (fin n) (fin n) ℤ)

@[simp] lemma id_comp : (id _).comp f = f :=
by simp only [comp, id, matrix.one_mul]

@[simp] lemma comp_id : g.comp (id _) = g :=
by simp only [comp, id, matrix.mul_one]

end basic_universal_map

@[derive add_comm_group]
def universal_map (m n : ℕ) := ℤ[basic_universal_map m n]

namespace universal_map
universe variable u

variables {k l m n : ℕ} (g : universal_map m n) (f : universal_map l m)
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

/-- Roughly speaking, this is a collection of formal finite sums of matrices
that encode that data that rolls out of the Breen--Deligne resolution. -/
structure data :=
(rank : ℕ → ℕ)
(map  : Π n, universal_map (rank (n+1)) (rank n))

def is_complex (BD : data) : Prop :=
∀ n, universal_map.comp (BD.map n) (BD.map (n+1)) = 0

/-
We use a small hack: mathlib only has block matrices with 4 blocks.
So we add two zero-width blocks in the definition of `σ_add` and `σ_proj`.
-/

def σ_add (n : ℕ) : universal_map (n + n) n :=
of $ matrix.reindex_linear_equiv (equiv.sum_empty _) sum_fin_sum_equiv $
matrix.from_blocks 1 1 0 0

def σ_proj (n : ℕ) : universal_map (n + n) n :=
(of $ matrix.reindex_linear_equiv (equiv.sum_empty _) sum_fin_sum_equiv $
matrix.from_blocks 1 0 0 0) +
(of $ matrix.reindex_linear_equiv (equiv.sum_empty _) sum_fin_sum_equiv $
matrix.from_blocks 0 1 0 0)

def σ_diff (n : ℕ) := σ_add n - σ_proj n

section
universe variables u
open universal_map
variables {m n : ℕ} (A : Type u) [add_comm_group A] (f : universal_map m n)

-- lemma eval_σ_add (n : ℕ) : eval A (σ_add n) = map (λ x, x.left + x.right) :=
-- begin
--   ext x, apply lift.ext; clear x, intro x,
--   delta σ_add,
--   rw [eval_of, basic_universal_map.eval_of],
--   congr' 1,
--   ext i,
--   simp only [pi.add_apply],
--   rw (sum_fin_sum_equiv.sum_comp _).symm,
--   swap, { apply_instance },
--   sorry
-- end

lemma σ_add_comp_double : comp (σ_add n) (double f) = comp f (σ_add m) :=
show add_monoid_hom.comp_hom ((@comp (m+m) (n+n) n) (σ_add _)) (double) f =
  (@comp (m+m) m n).flip (σ_add _) f,
begin
  congr' 1, clear f, ext1 f,
  show comp (σ_add n) (double (of f)) = comp (of f) (σ_add m),
  dsimp only [double_of, σ_add],
  simp only [comp_of],
  conv_rhs {
    rw ← (matrix.reindex_linear_equiv (equiv.sum_empty _) (equiv.sum_empty _)).apply_symm_apply f },
  simp only [basic_universal_map.comp, matrix.reindex_mul, matrix.from_blocks_multiply,
    add_zero, matrix.one_mul, matrix.mul_one, matrix.zero_mul, zero_add,
    matrix.reindex_linear_equiv_sum_empty_symm]
end

-- lemma eval_σ_proj (n : ℕ) : eval A (σ_proj n) = map tuple.left + map tuple.right :=
-- begin
--   ext x, apply lift.ext; clear x, intro x,
--   delta σ_proj,
--   simp only [add_monoid_hom.map_add, add_monoid_hom.add_apply,
--     eval_of, basic_universal_map.eval_of],
--   congr' 2,
--   { ext i,
--     rw [(sum_fin_sum_equiv.sum_comp _).symm, finset.sum_eq_single (sum.inl i)],
--     { dsimp, sorry },
--     all_goals { sorry } },
--   sorry
-- end

lemma σ_proj_comp_double : comp (σ_proj n) (double f) = comp f (σ_proj m) :=
show add_monoid_hom.comp_hom ((@comp (m+m) (n+n) n) (σ_proj _)) (double) f =
  (@comp (m+m) m n).flip (σ_proj _) f,
begin
  congr' 1, clear f, ext1 f,
  show comp (σ_proj n) (double (of f)) = comp (of f) (σ_proj m),
  dsimp only [double_of, σ_proj],
  simp only [add_monoid_hom.map_add, add_monoid_hom.add_apply, comp_of],
  conv_rhs {
    rw ← (matrix.reindex_linear_equiv (equiv.sum_empty _) (equiv.sum_empty _)).apply_symm_apply f },
  simp only [basic_universal_map.comp, matrix.reindex_mul, matrix.from_blocks_multiply,
    add_zero, matrix.one_mul, matrix.mul_one, matrix.zero_mul, matrix.mul_zero, zero_add,
    matrix.reindex_linear_equiv_sum_empty_symm],
end

lemma σ_diff_comp_double : comp (σ_diff n) (double f) = comp f (σ_diff m) :=
begin
  simp only [σ_diff, add_monoid_hom.map_sub, ← σ_add_comp_double, ← σ_proj_comp_double],
  simp only [sub_eq_add_neg, ← add_monoid_hom.neg_apply, ← add_monoid_hom.add_apply]
end

end

structure homotopy (BD : data) :=
(map         : Π n, universal_map (BD.rank n + BD.rank n) (BD.rank (n+1)))
(is_homotopy : ∀ n, σ_diff (BD.rank (n+1)) =
                universal_map.comp (BD.map (n+1)) (map (n+1)) +
                universal_map.comp (map n) (BD.map n).double)
(is_homotopy_zero : σ_add (BD.rank 0) - σ_proj (BD.rank 0) = universal_map.comp (BD.map 0) (map 0))
-- TODO! Is ↑ the thing we want?

structure package :=
(data       : data)
(is_complex : is_complex data)
(homotopy   : homotopy data)

namespace package

def rank (BD : package) := BD.data.rank

def map (BD : package) := BD.data.map

@[simp] lemma map_comp_map (BD : package) (n : ℕ) :
  universal_map.comp (BD.map n) (BD.map (n+1)) = 0 :=
BD.is_complex n

end package

namespace eg
/-! ## An explicit nontrivial example -/

open universal_map

def rank : ℕ → ℕ
| 0     := 1
| (n+1) := rank n + rank n

lemma rank_eq : ∀ n, rank n = 2 ^ n
| 0     := rfl
| (n+1) := by rw [pow_succ, two_mul, rank, rank_eq]

def map : Π n, universal_map (rank (n+1)) (rank n)
| 0     := σ_diff 1
| (n+1) := (σ_diff (rank (n+1))) - (map n).double

@[simps]
def data : data := ⟨rank, map⟩

def hmap (n : ℕ) : universal_map (rank n + rank n) (rank (n+1)) :=
universal_map.id _

lemma hmap_is_homotopy :
  ∀ n, σ_diff (rank (n+1)) =
  comp (map (n+1)) (hmap (n+1)) + comp (hmap n) (map n).double
| _ := by { simp only [hmap, id_comp, comp_id, map], simp only [sub_add_cancel], }

lemma hmap_is_homotopy_zero :
  σ_diff (rank 0) = universal_map.comp (map 0) (hmap 0) :=
begin
  simp only [hmap, id_comp, comp_id, map, σ_diff, σ_add, σ_proj, sub_sub],
  congr' 3;
  { ext (j : fin 1) (i : fin 2),
    fin_cases j, fin_cases i; refl }
end

@[simps]
def homotopy : homotopy data := ⟨hmap, hmap_is_homotopy, hmap_is_homotopy_zero⟩

lemma is_complex_zero :
  comp (map 0) (map 1) = 0 :=
begin
  show comp (σ_diff 1) (σ_diff (1+1) - double (σ_diff 1)) = 0,
  rw [add_monoid_hom.map_sub, σ_diff_comp_double, sub_self],
end

lemma is_complex_succ (n : ℕ) (ih : (comp (map n)) (map (n + 1)) = 0) :
  comp (map (n+1)) (map (n+1+1)) = 0 :=
begin
  have H := hmap_is_homotopy n,
  simp only [hmap, comp_id, id_comp] at H,
  show comp (map (n+1)) ((σ_diff (rank $ n+1+1)) - double (map (n+1))) = 0,
  simp only [add_monoid_hom.map_sub, ← σ_diff_comp_double, H],
  simp only [add_monoid_hom.map_add, add_monoid_hom.add_apply],
  simp only [comp_double_double, ih, double_zero, add_zero, sub_self],
end

lemma is_complex : is_complex data
| 0     := is_complex_zero
| (n+1) := is_complex_succ n (is_complex n)

end eg

/-- An example of a Breen--Deligne data coming from a nontrivial complex. -/
def eg : package := ⟨eg.data, eg.is_complex, eg.homotopy⟩

end breen_deligne
