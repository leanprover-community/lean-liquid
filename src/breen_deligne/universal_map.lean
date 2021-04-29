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

attribute [simps] equiv.sum_empty equiv.prod_punit equiv.punit_prod

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
  simp only [pi.add_apply, dmatrix.add_apply, add_smul, finset.sum_add_distrib],
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
    matrix.mul_apply, finset.sum_smul, mul_smul, add_monoid_hom.mk'_apply],
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

lemma mul_injective (N : ℕ) (hN : 0 < N) : function.injective (@mul m n N) :=
begin
  intros f g H,
  ext i j,
  rw function.funext_iff at H,
  specialize H (fin_prod_fin_equiv (⟨0, hN⟩, i)),
  rw function.funext_iff at H,
  specialize H (fin_prod_fin_equiv (⟨0, hN⟩, j)),
  dsimp [basic_universal_map.mul, matrix.kronecker] at H,
  simpa only [one_mul, equiv.symm_apply_apply, matrix.one_apply_eq] using H,
end

lemma mul_comp (N : ℕ) (g : basic_universal_map m n) (f : basic_universal_map l m) :
  mul N (comp g f) = comp (mul N g) (mul N f) :=
begin
  ext1 i j,
  dsimp only [mul, comp, add_monoid_hom.mk'_apply],
  rw [matrix.reindex_linear_equiv_mul, ← matrix.kronecker_mul, matrix.one_mul],
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
  dsimp only [comp, one_mul_hom, one_mul_inv, add_monoid_hom.mk'_apply, id],
  rw [matrix.reindex_linear_equiv_mul, matrix.one_mul, matrix.reindex_linear_equiv_one],
end

lemma one_mul_inv_hom : comp (one_mul_inv n) (one_mul_hom n) = id _ :=
begin
  dsimp only [comp, one_mul_hom, one_mul_inv, add_monoid_hom.mk'_apply, id],
  rw [matrix.reindex_linear_equiv_mul, matrix.one_mul, matrix.reindex_linear_equiv_one],
end

def mul_mul_hom (m n i : ℕ) : basic_universal_map (m * (n * i)) ((m * n) * i) :=
matrix.reindex_linear_equiv
  (((equiv.refl _).prod_congr fin_prod_fin_equiv.symm).trans $
    (equiv.prod_assoc _ _ _).symm.trans $ (fin_prod_fin_equiv.prod_congr $ equiv.refl _).trans
      fin_prod_fin_equiv)
  fin_prod_fin_equiv
  (1 : matrix (fin m × fin (n * i)) (fin m × fin (n * i)) ℤ)

def mul_mul_inv (m n i : ℕ) : basic_universal_map ((m * n) * i) (m * (n * i)) :=
matrix.reindex_linear_equiv
  fin_prod_fin_equiv
  (((equiv.refl _).prod_congr fin_prod_fin_equiv.symm).trans $
    (equiv.prod_assoc _ _ _).symm.trans $ (fin_prod_fin_equiv.prod_congr $ equiv.refl _).trans
      fin_prod_fin_equiv)
  (1 : matrix (fin m × fin (n * i)) (fin m × fin (n * i)) ℤ)

lemma mul_mul_hom_inv {m n i : ℕ} : comp (mul_mul_hom m n i) (mul_mul_inv m n i) = id _ :=
begin
  dsimp only [comp, mul_mul_hom, mul_mul_inv, add_monoid_hom.mk'_apply, id],
  rw [matrix.reindex_linear_equiv_mul, matrix.one_mul, matrix.reindex_linear_equiv_one],
end

lemma mul_mul_inv_hom {m n i : ℕ} : comp (mul_mul_inv m n i) (mul_mul_hom m n i) = id _ :=
begin
  dsimp only [comp, mul_mul_hom, mul_mul_inv, add_monoid_hom.mk'_apply, id],
  rw [matrix.reindex_linear_equiv_mul, matrix.one_mul, matrix.reindex_linear_equiv_one],
end

def proj_aux {N : ℕ} (k : fin N) : matrix punit.{1} (fin N) ℤ :=
λ i j, if j = k then 1 else 0

def proj (n : ℕ) {N : ℕ} (k : fin N) : basic_universal_map (N * n) n :=
matrix.reindex_linear_equiv (equiv.punit_prod _) fin_prod_fin_equiv $
matrix.kronecker (proj_aux k) 1

lemma proj_comp_mul {N : ℕ} (k : fin N) (f : basic_universal_map m n) :
  comp (proj n k) (mul N f) = comp f (proj m k) :=
begin
  dsimp only [comp, proj, mul, add_monoid_hom.mk'_apply],
  have : f = (matrix.reindex_linear_equiv
    (equiv.punit_prod (fin n)) (equiv.punit_prod (fin m)))
    (matrix.kronecker (1 : matrix punit.{1} punit.{1} ℤ) f),
  { ext i j,
    simp only [matrix.reindex_linear_equiv_apply, matrix.reindex_apply, matrix.minor_apply,
      equiv.punit_prod_symm_apply, matrix.kronecker, matrix.one_apply_eq, one_mul] },
  conv_rhs { rw this },
  simp only [matrix.reindex_linear_equiv_mul, ← matrix.kronecker_mul, matrix.one_mul, matrix.mul_one],
end

lemma one_mul_hom_eq_proj : basic_universal_map.one_mul_hom n = basic_universal_map.proj n 0 :=
begin
  dsimp only [basic_universal_map.one_mul_hom, basic_universal_map.proj],
  rw [← linear_equiv.symm_apply_eq, matrix.reindex_linear_equiv_symm, matrix.reindex_reindex,
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

lemma comp_proj_mul_proj (n N : ℕ) (j : fin (2 * 2 ^ N)) :
  (comp (proj n ((fin_prod_fin_equiv.symm) j).fst)) (mul 2 (proj n ((fin_prod_fin_equiv.symm) j).snd)) =
  (comp (proj n j)) (mul_mul_hom 2 (2 ^ N) n) :=
begin
  dsimp only [mul_mul_hom, proj, comp, mul_apply, add_monoid_hom.mk'_apply],
  rw [matrix.reindex_linear_equiv_mul, ← matrix.kronecker_mul, matrix.one_mul,
    matrix.kronecker_reindex_right, matrix.mul_one,
    matrix.kronecker_assoc', matrix.mul_reindex_linear_equiv_one, proj_aux_kronecker_proj_aux,
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

def bound : ℕ := ∑ g in f.support, (free_abelian_group.coeff g f).nat_abs

def bound_by (N : ℕ) : Prop := f.bound ≤ N

lemma of_bound_by (f : basic_universal_map m n) : bound_by (of f) 1 :=
begin
  simp only [bound_by, bound, coeff_of_self, int.nat_abs_one, finset.sum_singleton, support_of],
end

lemma zero_bound_by (N : ℕ) : (0 : universal_map m n).bound_by N :=
by simp only [bound_by, bound, zero_le', finset.sum_const_zero,
    add_monoid_hom.map_zero, int.nat_abs_zero]

lemma zero_bound_by_zero : (0 : universal_map m n).bound_by 0 :=
zero_bound_by _

lemma bound_by.random_index {f : universal_map m n} {N : ℕ}
  (hf : f.bound_by N) (s : finset (basic_universal_map m n)) :
  ∑ g in s, (free_abelian_group.coeff g f).nat_abs ≤ N :=
begin
  calc ∑ g in s, (free_abelian_group.coeff g f).nat_abs
      = ∑ g in s ∩ f.support, (free_abelian_group.coeff g f).nat_abs +
        ∑ g in s \ f.support, (free_abelian_group.coeff g f).nat_abs : _
  ... = ∑ g in s ∩ f.support, (free_abelian_group.coeff g f).nat_abs : _
  ... ≤ ∑ g in f.support ∩ s, (free_abelian_group.coeff g f).nat_abs +
        ∑ g in f.support \ s, (free_abelian_group.coeff g f).nat_abs : _
  ... ≤ ∑ g in f.support, (free_abelian_group.coeff g f).nat_abs : _
  ... ≤ N : hf,
  { rw finset.sum_inter_add_sum_diff },
  { simp only [and_imp, add_right_eq_self, int.nat_abs_eq_zero, imp_self, imp_true_iff,
      finset.mem_sdiff, finset.sum_eq_zero_iff, free_abelian_group.not_mem_support_iff] },
  { rw finset.inter_comm, simp only [le_add_iff_nonneg_right, zero_le'], },
  { rw finset.sum_inter_add_sum_diff },
end

lemma bound_by.add {f₁ f₂ : universal_map m n} {N₁ N₂ : ℕ}
  (h₁ : f₁.bound_by N₁) (h₂ : f₂.bound_by N₂) :
  (f₁ + f₂).bound_by (N₁ + N₂) :=
begin
  calc (f₁ + f₂).bound ≤
      ∑ (g : basic_universal_map m n) in support (f₁ + f₂),
        ((coeff g f₁).nat_abs + (coeff g f₂).nat_abs) : finset.sum_le_sum _
  ... ≤ N₁ + N₂ : _,
  { intros g hg,
    rw add_monoid_hom.map_add,
    apply int.nat_abs_add_le },
  { rw finset.sum_add_distrib,
    exact add_le_add (h₁.random_index _) (h₂.random_index _) }
end

lemma bound_by_sum {ι : Type*} (s : finset ι) (f : ι → universal_map m n) (N : ι → ℕ)
  (h : ∀ i ∈ s, (f i).bound_by (N i)) :
  (∑ i in s, f i).bound_by (∑ i in s, N i) :=
begin
  classical,
  revert h,
  apply finset.induction_on s; clear s,
  { simp only [finset.not_mem_empty, forall_false_left, finset.sum_empty,
      implies_true_iff, forall_true_left],
    exact zero_bound_by_zero },
  { intros i s his IH h,
    simp only [finset.sum_insert his],
    exact (h i $ s.mem_insert_self i).add (IH $ λ j hj, h j $ finset.mem_insert_of_mem hj) }
end

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

lemma mem_support_mul (N : ℕ) (hN : 0 < N) (f : universal_map m n) (g) :
  g ∈ (mul N f).support ↔ ∃ g', g' ∈ f.support ∧ g = basic_universal_map.mul N g' :=
begin
  apply free_abelian_group.mem_support_map,
  exact basic_universal_map.mul_injective N hN
end

@[simp]
lemma coeff_mul (N : ℕ) (hN : 0 < N) (f : universal_map m n) (g : basic_universal_map m n) :
  coeff (basic_universal_map.mul N g) (mul N f) = coeff g f :=
begin
  simp only [← add_monoid_hom.comp_apply],
  rw [← add_monoid_hom.comp_hom_apply_apply],
  congr' 1, clear f, ext f,
  simp only [comp_hom_apply_apply, function.comp_app, coe_comp, mul, coeff, to_finsupp_of,
    map_of', finsupp.apply_add_hom_apply, finsupp.single_apply,
    (basic_universal_map.mul_injective N hN).eq_iff],
  convert rfl
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
.

lemma proj_bound_by (n N : ℕ) : (proj n N).bound_by N :=
le_trans (bound_by_sum _ _ _ $ λ i _, of_bound_by _) $
by simp only [finset.card_fin, mul_one, algebra.id.smul_eq_mul, finset.sum_const]

end universal_map

end breen_deligne

-- #lint- only unused_arguments def_lemma doc_blame
