import linear_algebra.matrix
import group_theory.free_abelian_group
import algebra.direct_sum
import algebra.big_operators.finsupp

import for_mathlib.linear_algebra
import for_mathlib.free_abelian_group
import for_mathlib.kronecker

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

## Main definitions

- `breen_deligne.basic_universal_map` : the map corresponding to a matrix
- `breen_deligne.universal_map` : a formal linear combination of basic universal maps.

-/
noncomputable theory

-- get some notation working:
open_locale big_operators direct_sum

local attribute [instance] type_pow
local notation `ℤ[` A `]` := free_abelian_group A

namespace breen_deligne
open free_abelian_group


section move_this
variables {A : Type*}

attribute [simps] equiv.sum_empty equiv.prod_punit equiv.punit_prod

def L {m n : ℕ} (x : A ^ (m+n)) : A ^ m := λ i, x $ fin_sum_fin_equiv $ sum.inl i

def R {m n : ℕ} (x : A ^ (m+n)) : A ^ n := λ i, x $ fin_sum_fin_equiv $ sum.inr i

@[simps]
def split {m n : ℕ} : A ^ (m + n) ≃ A ^ m × A ^ n :=
{ to_fun := λ x, (L x, R x),
  inv_fun := λ x j, sum.elim x.1 x.2 (fin_sum_fin_equiv.symm j),
  left_inv := λ x, by { ext j, dsimp [L, R, fin_sum_fin_equiv], split_ifs with h h,
    { dsimp, cases j, refl, },
    { dsimp, cases j, congr, push_neg at h, rw nat.add_sub_cancel' h, refl } },
  right_inv := λ x,
  begin
    ext j; dsimp [L, R],
    { rw fin_sum_fin_equiv_symm_apply_left, swap, exact j.2, simp only [sum.elim_inl, fin.eta] },
    { ext j, rw fin_sum_fin_equiv_symm_apply_right, swap,
      { simp only [le_add_iff_nonneg_right, zero_le', fin.coe_mk] },
      { simp only [nat.add_sub_cancel_left, sum.elim_inr, fin.eta] } }
  end }

@[ext] lemma map_to_pi_add_ext
  {A B : Type*} {m n : ℕ} (f g : A → B ^ (m + n))
  (h1 : L ∘ f = L ∘ g) (h2 : R ∘ f = R ∘ g) :
  f = g :=
begin
  ext1 x, apply split.injective,
  revert x, rw [← function.funext_iff],
  rw [function.funext_iff] at h1 h2,
  ext1 x, ext1, { exact h1 x }, { exact h2 x }
end

end move_this

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

variables (A : Type*) [add_comm_group A]
variables {k l m n : ℕ} (g : basic_universal_map m n) (f : basic_universal_map l m)

def pre_eval : basic_universal_map m n →+ A^m → A^n :=
add_monoid_hom.mk' (λ f x i, ∑ j, f i j • (x : fin _ → A) j)
begin
  intros f₁ f₂,
  ext x i,
  simp only [matrix.add_apply, pi.add_apply, add_smul, finset.sum_add_distrib],
end

lemma pre_eval_apply : pre_eval A g = λ x i, ∑ j, g i j • (x : fin _ → A) j := rfl

/-- `f.eval A` for a `f : basic_universal_map m n`
is the homomorphism `ℤ[A^m] →+ ℤ[A^n]` induced by matrix multiplication. -/
def eval : ℤ[A^m] →+ ℤ[A^n] :=
map $ pre_eval A g

lemma eval_of (x : A^m) :
  g.eval A (of x) = (of $ pre_eval A g x) :=
lift.of _ _

/-- The composition of basic universal maps,
defined as matrix multiplication. -/
def comp : basic_universal_map m n →+ basic_universal_map l m →+ basic_universal_map l n :=
add_monoid_hom.mk' (λ g, add_monoid_hom.mk' (λ f, matrix.mul g f) $ matrix.mul_add _) $
  λ g₁ g₂, by { ext1 f, apply matrix.add_mul }

lemma eval_comp : (comp g f).eval A = (g.eval A).comp (f.eval A) :=
begin
  ext1 x,
  simp only [add_monoid_hom.coe_comp, function.comp_app, eval_of, pre_eval, comp, finset.smul_sum,
    matrix.mul_apply, finset.sum_smul, mul_smul, add_monoid_hom.coe_mk'],
  congr' 1,
  ext1 i,
  exact finset.sum_comm
end

lemma comp_assoc
  (h : basic_universal_map m n) (g : basic_universal_map l m) (f : basic_universal_map k l) :
  comp (comp h g) f = comp h (comp g f) :=
matrix.mul_assoc h g f

/-- The identity `basic_universal_map`. -/
def id (n : ℕ) : basic_universal_map n n := (1 : matrix (fin n) (fin n) ℤ)

@[simp] lemma id_comp : comp (id _) f = f :=
matrix.one_mul f

@[simp] lemma comp_id : comp g (id _) = g :=
matrix.mul_one g

/-- `double f` is the `universal_map` from `ℤ[A^m ⊕ A^m]` to `ℤ[A^n ⊕ A^n]`
given by applying `f` on both "components". -/
def double : basic_universal_map m n →+ basic_universal_map (m + m) (n + n) :=
add_monoid_hom.mk'
  (λ f, matrix.reindex_linear_equiv fin_sum_fin_equiv fin_sum_fin_equiv $
    matrix.from_blocks f 0 0 f)
  (λ f g, by rw [← linear_equiv.map_add, matrix.from_blocks_add, add_zero])

lemma comp_double_double (g : basic_universal_map m n) (f : basic_universal_map l m) :
  comp (double g) (double f) = double (comp g f) :=
by simp only [double, comp, add_monoid_hom.coe_mk', matrix.reindex_mul, matrix.from_blocks_multiply,
    matrix.zero_mul, matrix.mul_zero, add_zero, zero_add]

lemma pre_eval_double (f : basic_universal_map m n) :
  pre_eval A (double f) = (split.symm ∘ prod.map (pre_eval A f) (pre_eval A f) ∘ split) :=
begin
  ext1; ext x j; dsimp only [function.comp, L, R, double, pre_eval, add_monoid_hom.coe_mk'];
  rw [← fin_sum_fin_equiv.sum_comp, fintype.sum_sum_type];
  simp only [equiv.symm_apply_apply, sum.elim_inl, sum.elim_inr,
    split_symm_apply, split_apply, prod.map_mk,
    matrix.coe_reindex_linear_equiv, add_monoid_hom.coe_mk',
    matrix.from_blocks_apply₁₁, matrix.from_blocks_apply₁₂,
    matrix.from_blocks_apply₂₁, matrix.from_blocks_apply₂₂,
    pi.zero_apply, zero_smul, finset.sum_const_zero, add_zero, zero_add];
  refl
end

lemma eval_double (f : basic_universal_map m n) :
  eval A (double f) = (map $ split.symm ∘ prod.map (pre_eval A f) (pre_eval A f) ∘ split) :=
by rw [eval, pre_eval_double]

/-
We use a small hack: mathlib only has block matrices with 4 blocks.
So we add two zero-width blocks in the definition of `σ`, `π₁`, and `π₂`.
-/

/-- The basic universal map `ℤ[A^n ⊕ A^n] → ℤ[A^n]` that is first projection map. -/
def π₁ (n : ℕ) : basic_universal_map (n + n) n :=
matrix.reindex_linear_equiv (equiv.sum_empty _) fin_sum_fin_equiv $
matrix.from_blocks 1 0 0 0

/-- The basic universal map `ℤ[A^n ⊕ A^n] → ℤ[A^n]` that is second projection map. -/
def π₂ (n : ℕ) : basic_universal_map (n + n) n :=
matrix.reindex_linear_equiv (equiv.sum_empty _) fin_sum_fin_equiv $
matrix.from_blocks 0 1 0 0

@[simp] lemma π₁_comp_double (f : basic_universal_map m n) :
  comp (π₁ n) (double f) = comp f (π₁ m) :=
begin
  conv_rhs {
    rw ← (matrix.reindex_linear_equiv (equiv.sum_empty _) (equiv.sum_empty _)).apply_symm_apply f },
  dsimp only [π₁, double, comp, add_monoid_hom.coe_mk'],
  simp only [equiv.apply_symm_apply, matrix.reindex_mul, matrix.from_blocks_multiply,
    add_zero, matrix.one_mul, matrix.mul_one, matrix.zero_mul, matrix.mul_zero, zero_add,
    matrix.reindex_linear_equiv_sum_empty_symm],
end

@[simp] lemma π₂_comp_double (f : basic_universal_map m n) :
  comp (π₂ n) (double f) = comp f (π₂ m) :=
begin
  conv_rhs {
    rw ← (matrix.reindex_linear_equiv (equiv.sum_empty _) (equiv.sum_empty _)).apply_symm_apply f },
  dsimp only [π₂, double, comp, add_monoid_hom.coe_mk'],
  simp only [equiv.apply_symm_apply, matrix.reindex_mul, matrix.from_blocks_multiply,
    add_zero, matrix.one_mul, matrix.mul_one, matrix.zero_mul, matrix.mul_zero, zero_add,
    matrix.reindex_linear_equiv_sum_empty_symm],
end

lemma pre_eval_π₁ (n : ℕ) : pre_eval A (π₁ n) = L :=
begin
  ext x i,
  dsimp only [pre_eval, π₁, add_monoid_hom.coe_mk'],
  rw finset.sum_eq_single (fin_sum_fin_equiv $ sum.inl i),
  { rw [matrix.reindex_linear_equiv_apply, equiv.symm_apply_apply],
    dsimp only [equiv.sum_empty_symm_apply, matrix.from_blocks_apply₁₁],
    simp only [one_smul, matrix.one_apply_eq, L] },
  { rintro j - hj,
    simp only [matrix.reindex_linear_equiv_apply, equiv.symm_apply_apply],
    dsimp only [equiv.sum_empty_symm_apply],
    generalize hj' : fin_sum_fin_equiv.symm j = j',
    cases j' with j' j',
    { have : i ≠ j', { rintro rfl, apply hj, rw [← hj', equiv.apply_symm_apply] },
      simp only [matrix.from_blocks_apply₁₁, matrix.one_apply_ne this, zero_smul] },
    { simp only [matrix.from_blocks_apply₁₂, matrix.zero_apply, zero_smul] } },
  { intro h, exact (h (finset.mem_univ _)).elim }
end

lemma eval_π₁ (n : ℕ) : eval A (π₁ n) = map L :=
by rw [eval, pre_eval_π₁]

lemma pre_eval_π₂ (n : ℕ) : pre_eval A (π₂ n) = R :=
begin
  ext x i,
  dsimp only [pre_eval, π₂, add_monoid_hom.coe_mk'],
  rw finset.sum_eq_single (fin_sum_fin_equiv $ sum.inr i),
  { rw [matrix.reindex_linear_equiv_apply, equiv.symm_apply_apply],
    dsimp only [equiv.sum_empty_symm_apply, matrix.from_blocks_apply₁₂],
    simp only [one_smul, matrix.one_apply_eq, R] },
  { rintro j - hj,
    simp only [matrix.reindex_linear_equiv_apply, equiv.symm_apply_apply],
    dsimp only [equiv.sum_empty_symm_apply],
    generalize hj' : fin_sum_fin_equiv.symm j = j',
    cases j' with j' j',
    { simp only [matrix.from_blocks_apply₁₁, matrix.zero_apply, zero_smul] },
    { have : i ≠ j', { rintro rfl, apply hj, rw [← hj', equiv.apply_symm_apply] },
      simp only [matrix.from_blocks_apply₁₂, matrix.one_apply_ne this, zero_smul] } },
  { intro h, exact (h (finset.mem_univ _)).elim }
end

lemma eval_π₂ (n : ℕ) : eval A (π₂ n) = map R :=
by rw [eval, pre_eval_π₂]

def mul (N : ℕ) : basic_universal_map m n →+ basic_universal_map (N * m) (N * n) :=
add_monoid_hom.mk'
 (λ f, matrix.reindex_linear_equiv fin_prod_fin_equiv fin_prod_fin_equiv (matrix.kronecker 1 f))
begin
  intros f g,
  simp only [← matrix.kroneckerₗ_apply_apply, linear_map.map_add, linear_equiv.map_add],
end

lemma mul_apply (N : ℕ) (f : basic_universal_map m n) :
  mul N f = matrix.reindex_linear_equiv fin_prod_fin_equiv fin_prod_fin_equiv (matrix.kronecker 1 f) :=
rfl

lemma mul_comp (N : ℕ) (g : basic_universal_map m n) (f : basic_universal_map l m) :
  mul N (comp g f) = comp (mul N g) (mul N f) :=
begin
  ext1 i j,
  dsimp only [mul, comp, add_monoid_hom.coe_mk'],
  rw [matrix.reindex_mul, ← matrix.kronecker_mul, matrix.one_mul],
end

def one_mul_hom (n) : basic_universal_map (1 * n) n :=
matrix.reindex_linear_equiv
  ((fin_one_equiv.prod_congr $ equiv.refl _).trans $ equiv.punit_prod _)
  fin_prod_fin_equiv
  (1 : matrix (fin 1 × fin n) _ ℤ)

def one_mul_inv (n) : basic_universal_map n (1 * n) :=
matrix.reindex_linear_equiv
  fin_prod_fin_equiv
  ((fin_one_equiv.prod_congr $ equiv.refl _).trans $ equiv.punit_prod _)
  (1 : matrix (fin 1 × fin n) _ ℤ)

lemma one_mul_hom_inv : comp (one_mul_hom n) (one_mul_inv n) = id n :=
begin
  dsimp only [comp, one_mul_hom, one_mul_inv, add_monoid_hom.coe_mk', id],
  rw [matrix.reindex_mul, matrix.one_mul, matrix.reindex_one],
end

lemma one_mul_inv_hom : comp (one_mul_inv n) (one_mul_hom n) = id _ :=
begin
  dsimp only [comp, one_mul_hom, one_mul_inv, add_monoid_hom.coe_mk', id],
  rw [matrix.reindex_mul, matrix.one_mul, matrix.reindex_one],
end

def mul_mul_hom (m n i : ℕ) : basic_universal_map (m * (n * i)) ((m * n) * i) :=
matrix.reindex_linear_equiv
  -- (fin_prod_fin_equiv.trans $ (fin.cast $ (mul_assoc _ _ _).symm).to_equiv)
  (((equiv.refl _).prod_congr fin_prod_fin_equiv.symm).trans $
    (equiv.prod_assoc _ _ _).symm.trans $ (fin_prod_fin_equiv.prod_congr $ equiv.refl _).trans
      fin_prod_fin_equiv)
  fin_prod_fin_equiv
  (1 : matrix (fin m × fin (n * i)) (fin m × fin (n * i)) ℤ)

def mul_mul_inv (m n i : ℕ) : basic_universal_map ((m * n) * i) (m * (n * i)) :=
matrix.reindex_linear_equiv
  fin_prod_fin_equiv
  -- (fin_prod_fin_equiv.trans $ (fin.cast $ (mul_assoc _ _ _).symm).to_equiv)
  (((equiv.refl _).prod_congr fin_prod_fin_equiv.symm).trans $
    (equiv.prod_assoc _ _ _).symm.trans $ (fin_prod_fin_equiv.prod_congr $ equiv.refl _).trans
      fin_prod_fin_equiv)
  (1 : matrix (fin m × fin (n * i)) (fin m × fin (n * i)) ℤ)

lemma mul_mul_hom_inv {m n i : ℕ} : comp (mul_mul_hom m n i) (mul_mul_inv m n i) = id _ :=
begin
  dsimp only [comp, mul_mul_hom, mul_mul_inv, add_monoid_hom.coe_mk', id],
  rw [matrix.reindex_mul, matrix.one_mul, matrix.reindex_one],
end

lemma mul_mul_inv_hom {m n i : ℕ} : comp (mul_mul_inv m n i) (mul_mul_hom m n i) = id _ :=
begin
  dsimp only [comp, mul_mul_hom, mul_mul_inv, add_monoid_hom.coe_mk', id],
  rw [matrix.reindex_mul, matrix.one_mul, matrix.reindex_one],
end

def proj_aux {N : ℕ} (k : fin N) : matrix punit.{1} (fin N) ℤ :=
λ i j, if j = k then 1 else 0

def proj (n : ℕ) {N : ℕ} (k : fin N) : basic_universal_map (N * n) n :=
matrix.reindex_linear_equiv (equiv.punit_prod _) fin_prod_fin_equiv $
matrix.kronecker (proj_aux k) 1

lemma proj_comp_mul {N : ℕ} (k : fin N) (f : basic_universal_map m n) :
  comp (proj n k) (mul N f) = comp f (proj m k) :=
begin
  dsimp only [comp, proj, mul, add_monoid_hom.coe_mk'],
  have : f = (matrix.reindex_linear_equiv
    (equiv.punit_prod (fin n)) (equiv.punit_prod (fin m)))
    (matrix.kronecker (1 : matrix punit.{1} punit.{1} ℤ) f),
  { ext i j,
    simp only [matrix.reindex_linear_equiv_apply, equiv.punit_prod_symm_apply, matrix.kronecker,
      matrix.one_apply_eq, one_mul] },
  conv_rhs { rw this },
  simp only [matrix.reindex_mul, ← matrix.kronecker_mul, matrix.one_mul, matrix.mul_one],
end

lemma one_mul_hom_eq_proj : basic_universal_map.one_mul_hom n = basic_universal_map.proj n 0 :=
begin
  dsimp only [basic_universal_map.one_mul_hom, basic_universal_map.proj],
  rw [← linear_equiv.symm_apply_eq, matrix.reindex_symm, matrix.reindex_reindex,
    equiv.trans_symm, equiv.trans_assoc, equiv.trans_symm, equiv.trans_refl],
  ext ⟨i, i'⟩ ⟨j, j'⟩ : 2,
  change fin 1 at j,
  dsimp only [matrix.reindex_linear_equiv_apply, matrix.kronecker],
  dsimp [fin_one_equiv, equiv.prod_congr_left, basic_universal_map.proj_aux],
  simp only [matrix.one_apply, prod.mk.inj_iff, @eq_comm _ _ j],
  simp only [true_and, mul_boole, if_true, prod.mk.inj_iff,
    eq_self_iff_true, eq_iff_true_of_subsingleton],
  convert rfl
end
.

lemma proj_aux_kronecker_proj_aux (a :fin m) (b : fin n) :
  (proj_aux a).kronecker (proj_aux b) =
  matrix.reindex_linear_equiv (equiv.prod_punit _).symm fin_prod_fin_equiv.symm
    (proj_aux (fin_prod_fin_equiv (a,b))) :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩ : 2,
  dsimp [matrix.reindex_linear_equiv_apply, matrix.kronecker, proj_aux],
  simp only [equiv.apply_eq_iff_eq, boole_mul, prod.mk.inj_iff],
  symmetry,
  convert ite_and
end

-- -- move this
-- lemma prod.mk_fst_snd {α β : Type*} (x : α × β) : (x.1, x.2) = x :=
-- by squeeze_simp

lemma comp_proj_mul_proj (n N : ℕ) (j : fin (2 * 2 ^ N)) :
  (comp (proj n ((fin_prod_fin_equiv.symm) j).fst)) (mul 2 (proj n ((fin_prod_fin_equiv.symm) j).snd)) =
  (comp (proj n j)) (mul_mul_hom 2 (2 ^ N) n) :=
begin
  dsimp only [mul_mul_hom, proj, comp, mul_apply, add_monoid_hom.coe_mk'],
  rw [matrix.reindex_mul, ← matrix.kronecker_mul, matrix.one_mul,
    matrix.kronecker_reindex_right, matrix.mul_one,
    matrix.kronecker_assoc', matrix.mul_reindex_one, proj_aux_kronecker_proj_aux,
    matrix.kronecker_reindex_left],
  simp only [matrix.reindex_reindex],
  congr' 2,
  ext ⟨x, y⟩,
  dsimp,
  simp only [equiv.symm_apply_apply],
  rw [prod.mk.eta, equiv.apply_symm_apply],
end

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
of $ basic_universal_map.comp g f

@[simp] lemma comp_of (g : basic_universal_map m n) (f : basic_universal_map l m) :
  comp (of g) (of f) = of (basic_universal_map.comp g f) :=
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

def bound_by (N : ℕ) : Prop :=
∑ g in f.support, (free_abelian_group.coeff g f).nat_abs ≤ N

/-- `double f` is the `universal_map` from `ℤ[A^m ⊕ A^m]` to `ℤ[A^n ⊕ A^n]`
given by applying `f` on both "components". -/
def double : universal_map m n →+ universal_map (m + m) (n + n) :=
map $ basic_universal_map.double

lemma double_of (f : basic_universal_map m n) :
  double (of f) = of (basic_universal_map.double f) :=
rfl

lemma comp_double_double (g : universal_map m n) (f : universal_map l m) :
  comp (double g) (double f) = double (comp g f) :=
show comp_hom (comp_hom (comp_hom.flip (@double l m)) ((@comp (l+l) (m+m) (n+n)))) (double) g f =
     comp_hom (comp_hom (@double l n)) (@comp l m n) g f,
begin
  congr' 2, clear g f, ext g f : 2,
  show comp (double (of g)) (double (of f)) = double (comp (of g) (of f)),
  simp only [double_of, comp_of, basic_universal_map.comp_double_double]
end

lemma double_zero : double (0 : universal_map m n) = 0 :=
double.map_zero

open basic_universal_map

lemma eval_comp_double :
  (eval A).comp (@double m n) = (free_abelian_group.lift $ λ g,
    map $ split.symm ∘ prod.map (pre_eval A g) (pre_eval A g) ∘ split) :=
begin
  rw [double, eval],
  simp only [← basic_universal_map.eval_double],
  ext1 g, refl
end

lemma eval_double :
  eval A (double f) = (free_abelian_group.lift $ λ g,
    map $ split.symm ∘ prod.map (pre_eval A g) (pre_eval A g) ∘ split) f :=
by rw [← add_monoid_hom.comp_apply, eval_comp_double]

end

/-- The universal map `ℤ[A^n ⊕ A^n] → ℤ[A^n]` induced by the addition on `A^n`. -/
def σ (n : ℕ) : universal_map (n + n) n :=
of $ basic_universal_map.π₁ n + basic_universal_map.π₂ n

/-- The universal map `ℤ[A^n ⊕ A^n] → ℤ[A^n]` that is the sum of the projection maps. -/
def π (n : ℕ) : universal_map (n + n) n :=
(of $ basic_universal_map.π₁ n) + (of $ basic_universal_map.π₂ n)

lemma σ_comp_double (f : universal_map m n) :
  comp (σ n) (double f) = comp f (σ m) :=
show add_monoid_hom.comp_hom ((@comp (m+m) (n+n) n) (σ _)) (double) f =
  (@comp (m+m) m n).flip (σ _) f,
begin
  congr' 1, clear f, ext1 f,
  show comp (σ n) (double (of f)) = comp (of f) (σ m),
  dsimp only [double_of, σ],
  simp only [comp_of, add_monoid_hom.map_add, add_monoid_hom.add_apply,
    basic_universal_map.π₁_comp_double, basic_universal_map.π₂_comp_double],
end

lemma π_comp_double (f : universal_map m n) :
  comp (π n) (double f) = comp f (π m) :=
show add_monoid_hom.comp_hom ((@comp (m+m) (n+n) n) (π _)) (double) f =
  (@comp (m+m) m n).flip (π _) f,
begin
  congr' 1, clear f, ext1 f,
  show comp (π n) (double (of f)) = comp (of f) (π m),
  dsimp only [double_of, π],
  simp only [comp_of, add_monoid_hom.map_add, add_monoid_hom.add_apply,
    basic_universal_map.π₁_comp_double, basic_universal_map.π₂_comp_double],
end

lemma eval_σ (n : ℕ) : eval A (σ n) = map (L + R) :=
by simp only [σ, eval_of, basic_universal_map.eval, add_monoid_hom.map_add,
    basic_universal_map.pre_eval_π₁, basic_universal_map.pre_eval_π₂]

lemma eval_π (n : ℕ) : eval A (π n) = map L + map R :=
begin
  ext x,
  simp only [π, add_monoid_hom.map_add, map_of', add_monoid_hom.add_apply, eval_of,
    basic_universal_map.eval_π₁, basic_universal_map.eval_π₂],
end

section mul
open add_monoid_hom

def mul (N : ℕ) : universal_map m n →+ universal_map (N * m) (N * n) :=
map (basic_universal_map.mul N)

lemma mul_of (N : ℕ) (f : basic_universal_map m n) :
  mul N (of f) = of (basic_universal_map.mul N f) :=
map_of' _ _

lemma mul_comp (N : ℕ) (g : universal_map m n) (f : universal_map l m) :
  mul N (comp g f) = comp (mul N g) (mul N f) :=
begin
  simp only [← add_monoid_hom.comp_apply],
  rw [← add_monoid_hom.comp_hom_apply_apply, ← add_monoid_hom.comp_hom_apply_apply,
    ← add_monoid_hom.comp_hom_apply_apply,
    ← add_monoid_hom.flip_apply _ _ (mul N)],
  simp only [← add_monoid_hom.comp_apply],
  rw [← add_monoid_hom.comp_hom_apply_apply, ← add_monoid_hom.comp_hom_apply_apply],
  congr' 2, clear f g, ext g f,
  show (mul N) ((comp (of g)) (of f)) = (comp ((mul N) (of g))) ((mul N) (of f)),
  simp only [comp_of, mul_of, basic_universal_map.mul_comp],
end

end mul

def sum (n N : ℕ) : universal_map (N * n) n :=
of (∑ i, basic_universal_map.proj n i)

def proj (n N : ℕ) : universal_map (N * n) n :=
∑ i, of (basic_universal_map.proj n i)

lemma sum_comp_mul (N : ℕ) (f : universal_map m n) :
  comp (sum n N) (mul N f) = comp f (sum m N) :=
begin
  simp only [← add_monoid_hom.comp_apply],
  rw [← add_monoid_hom.comp_hom_apply_apply, ← add_monoid_hom.flip_apply _ _ (sum m N)],
  simp only [← add_monoid_hom.comp_apply],
  congr' 1, clear f, ext f,
  show (comp (sum n N)) ((mul N) (of f)) = (comp (of f)) (sum m N),
  simp only [sum, mul_of, comp_of, add_monoid_hom.map_sum,
    add_monoid_hom.finset_sum_apply, basic_universal_map.proj_comp_mul],
end

lemma proj_comp_mul (N : ℕ) (f : universal_map m n) :
  comp (proj n N) (mul N f) = comp f (proj m N) :=
begin
  simp only [← add_monoid_hom.comp_apply],
  rw [← add_monoid_hom.comp_hom_apply_apply, ← add_monoid_hom.flip_apply _ _ (proj m N)],
  simp only [← add_monoid_hom.comp_apply],
  congr' 1, clear f, ext f,
  show (comp (proj n N)) ((mul N) (of f)) = (comp (of f)) (proj m N),
  simp only [proj, mul_of, comp_of, add_monoid_hom.map_sum,
    add_monoid_hom.finset_sum_apply, basic_universal_map.proj_comp_mul],
end

end universal_map

end breen_deligne

-- #lint- only unused_arguments def_lemma doc_blame
