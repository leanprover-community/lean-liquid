import data.real.nnreal
import algebra.group.hom
import algebra.big_operators
import algebra.module.pi
import topology.basic

import hacks_and_tricks.type_pow

/-!

# Pseudo-normed groups

This file contains definitions and basic properties of pseudo-normed (abelian additive) groups.
See for example the comments after the proof of Proposition 9.10 of `analytic.pdf`, although we do
not work in an arbitrary topos.

## Main definitions

`pseudo_normed_group` -- a pseudo-normed abelian additive group

## Implementation issues

Right now we let the M_c be subsets of M. An alternative approach would be to have
them all as types; this is more convenient for some parts of the argument.

-/

noncomputable theory

open_locale nnreal big_operators

local attribute [instance] type_pow

/-- A pseudo-normed group is an abelian group `M`
together with an increasing filtration indexed by `ℝ≥0` of subsets `M_{≤c}`
containing `0` and closed under negation,
and such that if `x₁ ∈ M_{≤c₁}` and `x₂ ∈ M_{c₂}`, then `x₁ + x₂ ∈ M_{≤c₁ + c₂}`.

See also the comments after Proposition 9.10 on p66 in [Analytic].

Implementation details:
* In [Analytic], the filtration is indexed by *positive* real numbers (excluding) `0`,
  whereas this definition includes `0` in the indexing set.
* We do not ask for the filtration to be exhaustive (similar to [Analytic]),
  which is convenient, because it means that `M₁ →+ M₂` is naturally a pseudo-normed group
  if `M₁` and `M₂` are pseudo-normed groups. -/
class pseudo_normed_group (M : Type*) :=
[to_add_comm_group : add_comm_group M]
(filtration [] : ℝ≥0 → set M)
(filtration_mono : ∀ ⦃c₁ c₂⦄, c₁ ≤ c₂ → filtration c₁ ⊆ filtration c₂)
(zero_mem_filtration : ∀ c, (0:M) ∈ filtration c)
(neg_mem_filtration : ∀ ⦃c x⦄, x ∈ filtration c → (-x) ∈ filtration c)
(add_mem_filtration : ∀ ⦃c₁ c₂ x₁ x₂⦄,
  x₁ ∈ filtration c₁ → x₂ ∈ filtration c₂ → x₁ + x₂ ∈ filtration (c₁ + c₂))

/-- The additive commutative group instance underlying a pseudo-normed group. -/
add_decl_doc pseudo_normed_group.to_add_comm_group

open function

-- An alternative attempt at pseudo-normed groups,
-- that we might want to keep/switch to in the future

-- class pseudo_normed_group' (B_ : ℝ≥0 → Type*) (M : out_param Type*) :=
-- [to_add_comm_group : add_comm_group M]
-- [has_zero : Π r, has_zero (B_ r)]
-- [has_neg : Π r, has_neg (B_ r)]
-- (map : ∀ ⦃c₁ c₂⦄, c₁ ≤ c₂ → B_ c₁ → B_ c₂) -- rename
-- (incl : ∀ c, B_ c → M)
-- (incl_injective : ∀ c, injective (incl c))
-- (incl_zero : ∀ c, incl c 0 = 0)
-- (incl_neg : ∀ {c} (f : B_ c), incl c (-f) = - (incl c f))
-- (incl_map : ∀ {c₁ c₂} (h : c₁ ≤ c₂), (incl c₂) ∘ (map h) = (incl c₁))
-- (B_add {c₁ c₂} : B_ c₁ → B_ c₂ → B_ (c₁ + c₂))
-- (incl_add {c₁ c₂} (f : B_ c₁) (g : B_ c₂) : incl _ (B_add f g) = incl _ f + incl _ g)
-- (map_refl {c} : map (le_refl c) = id)
-- (map_trans {c₁ c₂ c₃} (h1 : c₁ ≤ c₂) (h2 : c₂ ≤ c₃) : map (h1.trans h2) = map h2 ∘ map h1)

/-
class topological_pseudo_normed_group' (B_ : ℝ≥0 → Type*) (M : Type*)
  extends pseudo_normed_group' B_ M :=
[is_top_space : Π r, topological_space (B_ r)]
-/


/-
Thought by Johan:
Maybe we want both defintions above, and write a bit of glue to move between them.
Both seem useful for different bits of what we want to do.
-/

attribute [instance] pseudo_normed_group.to_add_comm_group

namespace pseudo_normed_group

variables {M : Type*} [pseudo_normed_group M]

instance (c : ℝ≥0) : has_zero (filtration M c) := ⟨⟨0, zero_mem_filtration _⟩⟩
instance (c : ℝ≥0) : has_neg (filtration M c) := ⟨λ x, ⟨-x, neg_mem_filtration x.2⟩⟩

@[simp] lemma filtration.coe_zero {c : ℝ≥0} : ((0 : filtration M c) : M) = 0 := rfl
@[simp] lemma filtration.coe_neg {c : ℝ≥0} (x : filtration M c) :
  ((-x : filtration M c) : M) = -(x : M) := rfl

/-- Bounded uncurried addition for pseudo-normed groups. -/
def add' {c₁ c₂} (x : (filtration M c₁) × (filtration M c₂)) : filtration M (c₁ + c₂) :=
⟨(x.1 + x.2 : M), add_mem_filtration x.1.2 x.2.2⟩

@[simp] lemma add'_eq {c₁ c₂ : ℝ≥0} (x : (filtration M c₁) × (filtration M c₂)) :
  (add' x : M) = x.1 + x.2 := rfl

/-- Bounded negation for pseudo-normed groups. -/
def neg' {c} (x : filtration M c) : filtration M c :=
⟨(-x : M), neg_mem_filtration x.2⟩

@[simp] lemma neg'_eq {c : ℝ≥0} (x : filtration M c) :
  (neg' x : M) = -x := rfl

lemma sub_mem_filtration ⦃c₁ c₂ x₁ x₂⦄ (h₁ : x₁ ∈ filtration M c₁) (h₂ : x₂ ∈ filtration M c₂) :
  x₁ - x₂ ∈ filtration M (c₁ + c₂) :=
by { rw [sub_eq_add_neg], exact add_mem_filtration h₁ (neg_mem_filtration h₂) }

lemma neg_mem_filtration_iff (c x) : -x ∈ filtration M c ↔ x ∈ filtration M c :=
⟨λ h, by { rw [← neg_neg x], exact neg_mem_filtration h }, λ h, neg_mem_filtration h⟩

lemma sum_mem_filtration {ι : Type*} (x : ι → M) (c : ι → ℝ≥0) (s : finset ι)
  (h : ∀ i ∈ s, x i ∈ filtration M (c i)) :
  (∑ i in s, x i) ∈ filtration M (∑ i in s, (c i)) :=
begin
  classical,
  revert h, apply finset.induction_on s; clear s,
  { intro, simpa only [finset.sum_empty] using zero_mem_filtration _ },
  { intros i s his IH h,
    rw [finset.sum_insert his, finset.sum_insert his],
    apply add_mem_filtration (h _ _) (IH _),
    { exact finset.mem_insert_self i s },
    { intros j hj, apply h, exact finset.mem_insert_of_mem hj } }
end

lemma nat_smul_mem_filtration (n : ℕ) (m : M) (c : ℝ≥0) (h : m ∈ filtration M c) :
  (n • m) ∈ filtration M (n * c) :=
begin
  induction n with n ih, { simpa only [zero_smul] using zero_mem_filtration _ },
  simp only [nat.succ_eq_add_one, add_smul, one_smul, nat.cast_succ, add_mul, one_mul],
  exact add_mem_filtration ih h,
end

lemma int_smul_mem_filtration (n : ℤ) (m : M) (c : ℝ≥0) (h : m ∈ filtration M c) :
  (n • m) ∈ filtration M (n.nat_abs * c) :=
begin
  by_cases hn : 0 ≤ n,
  { lift n to ℕ using hn,
    simp only [int.nat_abs_of_nat, ← gsmul_eq_smul, gsmul_coe_nat, nsmul_eq_smul],
    exact pseudo_normed_group.nat_smul_mem_filtration n m c h },
  { push_neg at hn, rw ← neg_pos at hn,
    lift -n to ℕ using hn.le with k hk,
    rw [← neg_neg n, int.nat_abs_neg, ← hk, int.nat_abs_of_nat, neg_smul],
    apply neg_mem_filtration,
    simp only [neg_smul, ← gsmul_eq_smul, gsmul_coe_nat, nsmul_eq_smul],
    exact pseudo_normed_group.nat_smul_mem_filtration k m c h }
end

@[simps] def level {M₁ M₂ : Type*} [pseudo_normed_group M₁] [pseudo_normed_group M₂]
 (f : M₁ → M₂) (strict :  ∀ ⦃c x⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ c)
 (c : ℝ≥0) : filtration M₁ c → filtration M₂ c :=
λ x, ⟨f x, strict x.2⟩

section pi

variables

instance pi {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)] :
  pseudo_normed_group (Π i, M i) :=
{ filtration := λ c, { x | ∀ i, x i ∈ filtration (M i) c },
  filtration_mono := λ c₁ c₂ h x hx i, filtration_mono h (hx i),
  zero_mem_filtration := λ c i, zero_mem_filtration _,
  neg_mem_filtration := λ c x h i, neg_mem_filtration (h i),
  add_mem_filtration := λ c₁ c₂ x₁ x₂ h₁ h₂ i, add_mem_filtration (h₁ i) (h₂ i) }

lemma mem_filtration_pi {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)]
  (c : ℝ≥0) (x : Π i, M i) :
  x ∈ filtration (Π i, M i) c ↔ ∀ i, x i ∈ filtration (M i) c := iff.rfl

/-- The equivalence between `(Π i, M i)_c` and `Π i, (M i)_c`. -/
@[simps]
def filtration_pi_equiv {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)] (c : ℝ≥0) :
  filtration (Π i, M i) c ≃ Π i, filtration (M i) c :=
{ to_fun := λ x i, ⟨x.1 i, x.2 i⟩,
  inv_fun := λ x, ⟨λ i, x i, λ i, (x i).2⟩,
  left_inv := by { rintro ⟨x, hx⟩, refl },
  right_inv := by { intro x, ext, refl } }

end pi

section prod

variables (M₁ M₂ : Type*) [pseudo_normed_group M₁] [pseudo_normed_group M₂]

instance prod :
  pseudo_normed_group (M₁ × M₂) :=
{ filtration := λ c, { x | x.1 ∈ filtration M₁ c ∧ x.2 ∈ filtration M₂ c },
  filtration_mono := λ c₁ c₂ h x hx, ⟨filtration_mono h hx.1, filtration_mono h hx.2⟩,
  zero_mem_filtration := λ c, ⟨zero_mem_filtration _, zero_mem_filtration _⟩,
  neg_mem_filtration := λ c x h, ⟨neg_mem_filtration h.1, neg_mem_filtration h.2⟩,
  add_mem_filtration := λ c₁ c₂ x₁ x₂ h₁ h₂,
    ⟨add_mem_filtration h₁.1 h₂.1, add_mem_filtration h₁.2 h₂.2⟩ }

lemma mem_filtration_prod (c : ℝ≥0) (x : M₁ × M₂) :
  x ∈ filtration (M₁ × M₂) c ↔ x.1 ∈ filtration M₁ c ∧ x.2 ∈ filtration M₂ c := iff.rfl

/-- The equivalence between `(M₁ × M₂)_c` and `(M₁)_c × (M₂)_c`. -/
@[simps]
def filtration_prod_equiv (c : ℝ≥0) :
  filtration (M₁ × M₂) c ≃ filtration M₁ c × filtration M₂ c :=
{ to_fun := λ x, (⟨x.1.1,  x.2.1⟩, ⟨x.1.2, x.2.2⟩),
  inv_fun := λ x, ⟨(x.1, x.2), ⟨x.1.2, x.2.2⟩⟩,
  left_inv := by { rintro ⟨⟨x₁, x₂⟩, hx⟩, refl },
  right_inv := by { rintro ⟨x₁, x₂⟩, ext; refl } }

end prod

/-- The natural inclusion `filtration M c₁ → filtration M c₂`,
for a pseudo-normed group `M`, and `c₁ ≤ c₂`. -/
def cast_le {c₁ c₂ : ℝ≥0} [h : fact (c₁ ≤ c₂)] (x : filtration M c₁) :
  filtration M c₂ :=
⟨x, filtration_mono h.out x.2⟩

/-- The natural inclusion `filtration M c₁ → filtration M c₂`,
for a pseudo-normed group `M`, and `c₁ ≤ c₂`. -/
def cast_le' {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) : filtration M c₁ → filtration M c₂ :=
λ x, ⟨x, filtration_mono h x.2⟩

@[simp] lemma cast_le'_eq_cast_le {c₁ c₂ : ℝ≥0} [h : fact (c₁ ≤ c₂)] (x : filtration M c₁) :
  cast_le' h.out x = cast_le x := rfl

@[simp] lemma coe_cast_le {c₁ c₂ : ℝ≥0} [h : fact (c₁ ≤ c₂)] (x : filtration M c₁) :
  ((cast_le x : filtration M c₂) : M) = x := rfl

@[simp] lemma coe_cast_le' {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) (x : filtration M c₁) :
  ((cast_le' h x) : M) = x := rfl

lemma injective_cast_le (c₁ c₂ : ℝ≥0) [fact (c₁ ≤ c₂)] :
  function.injective (cast_le : filtration M c₁ → filtration M c₂) :=
λ x y h, subtype.coe_injective $
by simpa only [coe_cast_le] using congr_arg (coe : filtration M c₂ → M) h

variables (M)

end pseudo_normed_group

open pseudo_normed_group

namespace add_monoid_hom

variables {M M₁ M₂ M₃ : Type*}
variables [pseudo_normed_group M] [pseudo_normed_group M₁]
variables [pseudo_normed_group M₂] [pseudo_normed_group M₃]

instance : pseudo_normed_group (M₁ →+ M₂) :=
{ filtration := λ N, { f | ∀ ⦃c⦄ ⦃x : M₁⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ (N * c) },
  filtration_mono := λ N₁ N₂ h f hf c x hx, filtration_mono (mul_le_mul_right' h c) (hf hx),
  zero_mem_filtration := λ N c x hx, zero_mem_filtration _,
  neg_mem_filtration := λ N f hf c x hx, neg_mem_filtration $ hf hx,
  add_mem_filtration := λ N₁ N₂ f₁ f₂ hf₁ hf₂ c x hx,
  by { rw add_mul, apply add_mem_filtration (hf₁ hx) (hf₂ hx) },
  .. add_monoid_hom.add_comm_group }

lemma comp_mem_filtration {g f cg cf}
  (hg : g ∈ filtration (M₂ →+ M₃) cg) (hf : f ∈ filtration (M₁ →+ M₂) cf) :
  g.comp f ∈ filtration (M₁ →+ M₃) (cg * cf) :=
λ c x hx, by { rw mul_assoc, exact hg (hf hx) }

@[simp] lemma id_mem_filtration (c : ℝ≥0) (hc : 1 ≤ c) : id M ∈ filtration (M →+ M) c :=
λ c' x hx, by refine filtration_mono _ hx;
calc c' = 1 * c' : by rw one_mul
    ... ≤ c * c' : mul_le_mul_right' hc c'

-- move this, maybe it already exists?
/-- The additive monoid homomorphism into a product of additive monoids,
constructed from a family of monoid homomorphisms into the factors. -/
@[simps {rhs_md:=semireducible, fully_applied:=ff}]
def mk_to_pi {M₁} [add_monoid M₁] {ι : Type*} {M : ι → Type*} [Π i, add_monoid (M i)]
  (f : Π i, M₁ →+ (M i)) :
  M₁ →+ (Π i, M i) :=
{ to_fun := λ v i, f i v,
  map_zero' := by { simp only [map_zero], refl },
  map_add' := by { intros, simp only [map_add], refl } }

lemma mk_to_pi_mem_filtration {ι : Type*} {M : ι → Type*}
  [Π i, pseudo_normed_group (M i)] (f : Π i, M₁ →+ (M i))
  {c} (hfc : ∀ i, f i ∈ filtration (M₁ →+ (M i)) c) :
  mk_to_pi f ∈ filtration (M₁ →+ (Π i, M i)) c :=
λ c' x h i, hfc i h

lemma eval_mem_filtration {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)]
  (i : ι) (c : ℝ≥0) (hc : 1 ≤ c) :
  (pi.eval_add_monoid_hom M i) ∈ filtration ((Π i, M i) →+ M i) c :=
λ c' x hx, by refine filtration_mono _ (hx i);
calc c' = 1 * c' : by rw one_mul
    ... ≤ c * c' : mul_le_mul_right' hc c'

/-- The additive monoid homomorphism out of a finite product of additive monoids,
constructed from a family of monoid homomorphisms out of the factors. -/
def mk_from_pi {ι : Type*} [fintype ι] {M : ι → Type*} {M₂}
  [Π i, add_monoid (M i)] [add_comm_monoid M₂] (f : Π i, (M i) →+ M₂) :
  (Π i, M i) →+ M₂ :=
∑ i, (f i).comp (pi.eval_add_monoid_hom M i)

@[simp] lemma mk_from_pi_apply {ι : Type*} [fintype ι] {M : ι → Type*} [Π i, add_comm_monoid (M i)]
  (f : Π i, M i →+ M₂) (x : Π i, M i) :
  mk_from_pi f x = (∑ i, f i (x i)) :=
begin
  show add_monoid_hom.eval x (mk_from_pi f) = _,
  simp only [mk_from_pi, add_monoid_hom.map_sum],
  refl
end

@[simp] lemma coe_mk_from_pi {ι : Type*} [fintype ι] {M : ι → Type*} [Π i, add_comm_monoid (M i)]
  (f : Π i, M i →+ M₂) :
  ⇑(mk_from_pi f) = ∑ i, (f i ∘ pi.eval_add_monoid_hom M i) :=
by { ext x, rw [@mk_from_pi_apply M₂ _ ι _ M _ f x, fintype.sum_apply], refl }

lemma mk_from_pi_mem_filtration {ι : Type*} [fintype ι] {M : ι → Type*}
  [Π i, pseudo_normed_group (M i)] (f : Π i, (M i) →+ M₂)
  {c : ι → ℝ≥0} (hfc : ∀ i, f i ∈ filtration ((M i) →+ M₂) (c i)) :
  (mk_from_pi f) ∈ filtration ((Π i, M i) →+ M₂) (∑ i, c i) :=
λ c' x h,
begin
  rw [finset.sum_mul, @mk_from_pi_apply M₂ _ ι _ M _ f x],
  refine sum_mem_filtration _ _ _ _,
  rintro i -,
  exact hfc i (h i)
end

lemma const_smul_hom_nat_mem_filtration (n : ℕ) (c : ℝ≥0) (h : ↑n ≤ c) :
  distrib_mul_action.to_add_monoid_hom M n ∈ filtration (M →+ M) c :=
λ c' x hx, by simpa only [distrib_mul_action.to_add_monoid_hom_apply]
  using filtration_mono (mul_le_mul_right' h c') (nat_smul_mem_filtration _ _ _ hx)

lemma const_smul_hom_int_mem_filtration (n : ℤ) (c : ℝ≥0) (h : ↑(n.nat_abs) ≤ c) :
  distrib_mul_action.to_add_monoid_hom M n ∈ filtration (M →+ M) c :=
λ c' x hx, by simpa only [distrib_mul_action.to_add_monoid_hom_apply]
  using filtration_mono (mul_le_mul_right' h c') (int_smul_mem_filtration _ _ _ hx)

end add_monoid_hom

namespace pseudo_normed_group

section splittable

class splittable (M : Type*) [pseudo_normed_group M] (N : ℕ) (d : ℝ≥0) :=
(exists_sum : ∀ (c : ℝ≥0) (x : M) (hx : x ∈ filtration M c),
  ∃ y : fin N → M, (x = ∑ i, y i) ∧ (∀ i, y i ∈ filtration M (c/N + d)))

variables {M : Type*} [pseudo_normed_group M] (N : ℕ) (d : ℝ≥0) [splittable M N d]

lemma exists_sum (c : ℝ≥0) (x : M) (hx : x ∈ filtration M c) :
  ∃ y : fin N → M, (x = ∑ i, y i) ∧ (y ∈ filtration (M^N) (c/N + d)) :=
splittable.exists_sum c x hx

instance splittable_pi {ι : Type*} (M : ι → Type*) [Π i, pseudo_normed_group (M i)]
  (N : ℕ) (d : ℝ≥0) [∀ i, splittable (M i) N d] :
  splittable (Π i, M i) N d :=
{ exists_sum := λ c x hx,
  begin
    have := λ i, exists_sum N d c (x i) (hx i),
    choose y hy1 hy2 using this,
    refine ⟨swap y, _, swap hy2⟩,
    ext i, rw [hy1], symmetry, convert finset.sum_apply i _ _,
  end }

end splittable

end pseudo_normed_group


-- #lint- only unused_arguments def_lemma doc_blame
