import analysis.normed_space.banach
import analysis.mean_inequalities_pow

import normed_group.normed_with_aut

/-!
# p-Banach spaces

A `p`-Banach space is just like an ordinary Banach space,
except that the axiom `∥c • v∥ = ∥c∥ * ∥v∥` is replaced by `∥c • v∥ = ∥c∥^p * ∥v∥`.

In other words, a `p`-Banach space is a complete topological vector space
whose topology is induced by a `p`-norm.


In this file, we define `p`-normed spaces, called `normed_space'`,
and we prove that every `p`-normed space is also `p'`-normed, for `0 < p' ≤ p`.

-/

noncomputable theory

open_locale nnreal

section

structure has_p_norm (V : Type*) (p : ℝ)
  [add_comm_group V] [module ℝ V] [uniform_space V] extends has_norm V :=
(norm_smul : ∀ (α : ℝ) (v : V), ∥α • v∥ = |α|^p • ∥v∥)
(triangle : ∀ (v w : V), ∥v+w∥ ≤ ∥v∥ + ∥w∥)
(uniformity : uniformity V = ⨅ (ε : ℝ) (H : ε > 0),
  filter.principal {p : V × V | ∥p.fst - p.snd∥ < ε})

variables (V : Type*) (p : ℝ) [fact (0 < p)] [add_comm_group V] [module ℝ V] [uniform_space V]

def has_p_norm.semi_normed_group (h : has_p_norm V p) : semi_normed_group V :=
{ to_uniform_space := by apply_instance,
  uniformity_dist := h.uniformity,
  to_add_comm_group := by apply_instance,
  .. @semi_normed_group.of_core V _ h.to_has_norm $
    have hp0 : p ≠ 0 := (fact.out _ : 0 < p).ne',
    { norm_zero := by simpa only [zero_smul, abs_zero, real.zero_rpow hp0] using h.norm_smul 0 0,
      triangle := h.triangle,
      norm_neg := λ v, by simpa only [neg_smul, one_smul, abs_neg, abs_one, real.one_rpow]
                            using h.norm_smul (-1) v } }

structure p_banach : Prop :=
(exists_p_norm : nonempty (has_p_norm V p))
[topological_add_group : topological_add_group V]
[continuous_smul : has_continuous_smul ℝ V]
[complete : complete_space V]

end

structure pBanach (p : ℝ) [fact (0 < p)] :=
(V : Type*)
[add_comm_group' : add_comm_group V]
[module' : module ℝ V]
[uniform_space' : uniform_space V]
(p_banach' : p_banach V p)

namespace pBanach

variables (p : ℝ) [fact (0 < p)] (V : pBanach p)

instance : has_coe_to_sort (pBanach p) (Type*) := ⟨λ X, X.V⟩

instance : _root_.add_comm_group V := V.add_comm_group'
instance : _root_.module ℝ V := V.module'
instance : _root_.uniform_space V := V.uniform_space'
instance : _root_.topological_add_group V := V.p_banach'.topological_add_group
instance : _root_.has_continuous_smul ℝ V := V.p_banach'.continuous_smul
instance : _root_.complete_space V := V.p_banach'.complete

variables {p}

/-- Highly non-canonical! -/
def choose_semi_normed_group : semi_normed_group V :=
(classical.choice V.p_banach'.exists_p_norm).semi_normed_group V p

@[simps] def smul_normed_hom (x : ℝ) :
  @normed_group_hom V V V.choose_semi_normed_group V.choose_semi_normed_group :=
{ to_fun := λ v, x • v,
  map_add' := λ v₁ v₂, smul_add _ _ _,
  bound' := ⟨|x|^p, λ v, by rw [has_p_norm.norm_smul, smul_eq_mul]⟩ }

/-- Highly non-canonical! -/
def choose_normed_with_aut (x : ℝ≥0) [fact (0 < x)] :
  normed_with_aut (x ^ p) ⟨V, choose_semi_normed_group V⟩ :=
{ T :=
  { hom := smul_normed_hom V x,
    inv := smul_normed_hom V (x⁻¹),
    hom_inv_id' := by { ext v, dsimp, rw [← mul_smul, inv_mul_cancel, one_smul],
      exact_mod_cast (fact.out _ : 0 < x).ne' },
    inv_hom_id' := by { ext v, dsimp, rw [← mul_smul, mul_inv_cancel, one_smul],
      exact_mod_cast (fact.out _ : 0 < x).ne' } } ,
  norm_T := λ v, by { dsimp, rw [has_p_norm.norm_smul, smul_eq_mul], congr' 2,
    rw abs_eq_self, exact x.coe_nonneg } }

@[simp]
lemma choose_normed_with_aut_T_hom (x : ℝ≥0) [fact (0 < x)] (v : V) :
  (@normed_with_aut.T (x ^ p) ⟨V, choose_semi_normed_group V⟩ (V.choose_normed_with_aut x)).hom v =
  x • v := rfl

@[simp]
lemma choose_normed_with_aut_T_inv (x : ℝ≥0) [fact (0 < x)] (v : V) :
  (@normed_with_aut.T (x ^ p) ⟨V, choose_semi_normed_group V⟩ (V.choose_normed_with_aut x)).inv v =
  x⁻¹ • v := rfl

end pBanach

-- noncomputable
-- def pBanach'_is_qBanach' (V: Type*) (p : ℝ) [fact (0 < p)] [fact (p ≤ 1)] (q : ℝ) [fact (0 < q)]
--   [fact (q ≤ 1)] [add_comm_group V] [module ℝ V] [uniform_space V] [has_continuous_smul ℝ V]
--   [topological_add_group V] [complete_space V] (hp : pBanach' V p) : pBanach' V q :=
-- begin
--   cases hp,
--   let Hp_norm := hp.some,
--   let ψ := Hp_norm.norm,
--   use λ v : V, (ψ v)^(q/p),--[FAE] Why λ v, ((h_p_norm.norm) v)^(q/p) does not work?
--   intros α v,
--   dsimp only [ψ],
--   admit,
--   admit,
  -- rw [Hp_norm.p_norm α v, smul_eq_mul, real.mul_rpow, ← real.rpow_mul, mul_div_cancel'],
  -- exacts [refl _, ne_of_gt (fact.out _), abs_nonneg α,
  --   (real.rpow_nonneg_of_nonneg (abs_nonneg α) p), hp_nonneg_norm v,
  --   (λ _, (real.rpow_nonneg_of_nonneg (hp_nonneg_norm _) _))],
-- end


section obsolete

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

end obsolete
