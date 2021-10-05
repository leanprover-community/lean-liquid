import analysis.normed_space.banach
import analysis.mean_inequalities

/-!
# p-Banach spaces

A `p`-Banach space is just like an ordinary Banach space,
except that the axiom `∥c • v∥ = ∥c∥ * ∥v∥` is replaced by `∥c • v∥ = ∥c∥^p * ∥v∥`

In this file, we define `p`-normed spaces, called `normed_space'`,
and we prove that every `p`-normed space is also `p'`-normed, for `0 < p' ≤ p`.

-/

noncomputable theory

open_locale nnreal

-- move this
lemma real.add_rpow_le {x y r : ℝ}
  (hx : 0 ≤ x) (hy : 0 ≤ y) (h0r : 0 ≤ r) (hr1 : r ≤ 1) :
  (x + y)^r ≤ x^r + y^r :=
begin
  by_cases hr : 0 = r,
  { subst r, simp only [zero_le_one, real.rpow_zero, le_add_iff_nonneg_left], },
  let x' : ℝ≥0 := ⟨x, hx⟩,
  let y' : ℝ≥0 := ⟨y, hy⟩,
  exact_mod_cast ennreal.rpow_add_le_add_rpow x' y' (lt_of_le_of_ne h0r hr) hr1,
end

set_option extends_priority 920
-- Here, we set a rather high priority for the instance `[normed_space α β] : module α β`
-- to take precedence over `semiring.to_module` as this leads to instance paths with better
-- unification properties.
/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class normed_space' (𝕜 : Type*) (p : out_param ℝ) (V : Type*)
  [normed_field 𝕜] [normed_group V] [module 𝕜 V] :=
(norm_smul : ∀ (c:𝕜) (v:V), ∥c • v∥ = ∥c∥^p * ∥v∥)

@[priority 100]
instance normed_space.normed_space'
  (𝕜 : Type*) (V : Type*) [normed_field 𝕜] [normed_group V] [normed_space 𝕜 V] :
  normed_space' 𝕜 1 V :=
{ norm_smul := λ c k, by simp only [real.rpow_one, norm_smul] }

/-- A type alias: `as_normed_space' p' V` is a `p'`-normed space over `𝕜`,
when `V` is a `p`-normed space over `𝕜` and `0 < p' ≤ p`. -/
@[nolint unused_arguments]
def as_normed_space' (p' : ℝ) (V : Type*) := V

namespace as_normed_space'

instance (p' : ℝ) (V : Type*) [i : inhabited V] : inhabited (as_normed_space' p' V) := i

/-- The identity map `V → as_normed_space' p' V`. -/
def up (p' : ℝ) {V : Type*} (v : V) : as_normed_space' p' V := v

/-- The identity map `as_normed_space' p' V → V`. -/
def down {p' : ℝ} {V : Type*} (v : as_normed_space' p' V) : V := v

instance (p' : ℝ) (V : Type*) [i : add_comm_group V] : add_comm_group (as_normed_space' p' V) := i

instance (p' : ℝ) (𝕜 V : Type*) [ring 𝕜] [add_comm_group V] [i : module 𝕜 V] :
  module 𝕜 (as_normed_space' p' V) := i

@[simp] lemma down_add {p' : ℝ} {V : Type*} [add_comm_group V] (v w : as_normed_space' p' V) :
  (v+w).down = v.down + w.down := rfl

@[simp] lemma down_neg {p' : ℝ} {V : Type*} [add_comm_group V] (v : as_normed_space' p' V) :
  (-v).down = - v.down := rfl

@[simp] lemma down_smul {p' : ℝ} {𝕜 V : Type*} [ring 𝕜] [add_comm_group V] [module 𝕜 V]
  (c : 𝕜) (v : as_normed_space' p' V) :
  (c • v).down = c • v.down := rfl

/-- The natural `p'`-norm on `as_normed_space' p' V` induced by a `p`-norm on `V`. -/
protected def has_norm (p' p : ℝ) (V : Type*) [has_norm V] :
  has_norm (as_normed_space' p' V) :=
⟨λ v, ∥v.down∥^(p'/p)⟩

lemma norm_def {V : Type*} [has_norm V] (p' p : ℝ) (v : as_normed_space' p' V) :
  @has_norm.norm _ (as_normed_space'.has_norm p' p V) v = ∥v.down∥^(p'/p) := rfl

/-- The natural `p'`-normed group structure on `as_normed_space' p' V`
induced by a `p`-normed group structure on `V` -/
protected def normed_group (V : Type*) [normed_group V] (p' p : ℝ) [fact (0 < p')] [fact (p' ≤ p)] :
  normed_group (as_normed_space' p' V) :=
@normed_group.of_core _ _ (as_normed_space'.has_norm p' p V) $
have hp' : 0 < p'   := fact.out _,
have hp  : 0 < p    := lt_of_lt_of_le hp' (fact.out _),
have H   : 0 < p'/p := div_pos hp' hp,
{ norm_eq_zero_iff := λ v, show ∥v.down∥^(p'/p) = 0 ↔ v = 0,
  by simpa only [real.rpow_eq_zero_iff_of_nonneg (norm_nonneg v.down), norm_eq_zero,
        H.ne', and_true, ne.def, not_false_iff],
  triangle := λ v w, show ∥(v+w).down∥^(p'/p) ≤ ∥v.down∥^(p'/p) + ∥w.down∥^(p'/p),
  begin
    rw [down_add],
    calc ∥v.down + w.down∥ ^ (p' / p)
        ≤ (∥v.down∥ + ∥w.down∥) ^ (p' / p) : real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) H.le
    ... ≤ ∥v.down∥ ^ (p' / p) + ∥w.down∥ ^ (p' / p) :
      real.add_rpow_le (norm_nonneg _) (norm_nonneg _) H.le _,
    rw [div_le_iff hp, one_mul],
    exact fact.out _
  end,
  norm_neg := λ v, show ∥(-v).down∥^(p'/p) = ∥v.down∥^(p'/p), by rw [down_neg, norm_neg] }

local attribute [instance] as_normed_space'.normed_group

instance (𝕜 : Type*) (V : Type*) [normed_field 𝕜] [normed_group V] [module 𝕜 V]
  (p' p : ℝ) [fact (0 < p')] [fact (p' ≤ p)] [normed_space' 𝕜 p V] :
  normed_space' 𝕜 p' (as_normed_space' p' V) :=
{ norm_smul := λ c v,
  begin
    have hp' : 0 < p'   := fact.out _,
    have hp  : 0 < p    := lt_of_lt_of_le hp' (fact.out _),
    rw [norm_def, norm_def, down_smul, normed_space'.norm_smul, real.mul_rpow, ← real.rpow_mul,
      mul_div_cancel' _ hp.ne'],
    { exact norm_nonneg _ },
    { exact real.rpow_nonneg_of_nonneg (norm_nonneg _) _ },
    { exact norm_nonneg _ },
  end }

end as_normed_space'

variables (p : ℝ≥0)

structure pBanach :=
(V : Type*)
(is_normed_group : normed_group V)
(is_module : module ℝ V)
(is_normed_space' : normed_space' ℝ p V)

namespace pBanach

instance : has_coe_to_sort (pBanach p) :=
{ S := Type*,
  coe := λ X, X.V }

instance (X : pBanach p) : normed_group X := X.is_normed_group
instance (X : pBanach p) : module ℝ X := X.is_module
instance (X : pBanach p) : normed_space' ℝ p X := X.is_normed_space'

end pBanach
