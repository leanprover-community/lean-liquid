import breen_deligne.universal_map

namespace breen_deligne

open free_abelian_group

/-- Roughly speaking, this is a collection of formal finite sums of matrices
that encode that data that rolls out of the Breen--Deligne resolution. -/
structure data :=
(rank : ℕ → ℕ)
(map  : Π n, universal_map (rank (n+1)) (rank n))

/-- Breen--Deligne data is a complex
if the composition of all pairs of two subsequent maps in the data is `0`. -/
def is_complex (BD : data) : Prop :=
∀ n, universal_map.comp (BD.map n) (BD.map (n+1)) = 0

/-
We use a small hack: mathlib only has block matrices with 4 blocks.
So we add two zero-width blocks in the definition of `σ_add` and `σ_proj`.
-/

/-- The universal map `ℤ[A^n ⊕ A^n] → ℤ[A^n]`
induced by the addition on `A^n`. -/
def σ_add (n : ℕ) : universal_map (n + n) n :=
of $ matrix.reindex_linear_equiv (equiv.sum_empty _) sum_fin_sum_equiv $
matrix.from_blocks 1 1 0 0

/-- The universal map `ℤ[A^n ⊕ A^n] → ℤ[A^n]`
that is the formal sum of the two projection maps. -/
def σ_proj (n : ℕ) : universal_map (n + n) n :=
(of $ matrix.reindex_linear_equiv (equiv.sum_empty _) sum_fin_sum_equiv $
matrix.from_blocks 1 0 0 0) +
(of $ matrix.reindex_linear_equiv (equiv.sum_empty _) sum_fin_sum_equiv $
matrix.from_blocks 0 1 0 0)

/-- The universal map `ℤ[A^n ⊕ A^n] → ℤ[A^n]`
that is the difference between `σ_diff` (induced by the addition on `A^n`)
and `σ_proj` (the formal sum of the two projections). -/
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
--   admit
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
--     { dsimp, admit },
--     all_goals { admit } },
--   admit
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

/-- A `homotopy` for Breen--Deligne data `BD` consists of maps `map n`,
for each natural number `n`, that constitute a homotopy between
the two universal maps `σ_add` and `σ_proj`. -/
structure homotopy (BD : data) :=
(map         : Π n, universal_map (BD.rank n + BD.rank n) (BD.rank (n+1)))
(is_homotopy : ∀ n, σ_diff (BD.rank (n+1)) =
                universal_map.comp (BD.map (n+1)) (map (n+1)) +
                universal_map.comp (map n) (BD.map n).double)
(is_homotopy_zero : σ_add (BD.rank 0) - σ_proj (BD.rank 0) = universal_map.comp (BD.map 0) (map 0))
-- TODO! Is ↑ the thing we want?


/-- `BD.double` is the Breen--Deligne data whose `n`-th rank is `2 * BD.rank n`. -/
@[simps] def data.double (BD : data) : data :=
{ rank := λ n, BD.rank n + BD.rank n,
  map := λ n, (BD.map n).double }

/-- `BD.pow N` is the Breen--Deligne data whose `n`-th rank is `2^N * BD.rank n`. -/
def data.pow (BD : data) : ℕ → data
| 0     := BD
| (n+1) := (data.pow n).double

/-- A Breen--Deligne `package` consists of Breen--Deligne `data`
that forms a complex, together with a `homotopy`
between the two universal maps `σ_add` and `σ_proj`. -/
structure package :=
(data       : data)
(is_complex : is_complex data)
(homotopy   : homotopy data)

namespace package

/-- `BD.rank i` is the rank of the `i`th entry in the Breen--Deligne resolution described by `BD`. -/
def rank (BD : package) := BD.data.rank

/-- `BD.map i` is the `i`-th universal mapin the Breen--Deligne resolution described by `BD`. -/
def map (BD : package) := BD.data.map

@[simp] lemma map_comp_map (BD : package) (n : ℕ) :
  universal_map.comp (BD.map n) (BD.map (n+1)) = 0 :=
BD.is_complex n

end package

end breen_deligne
