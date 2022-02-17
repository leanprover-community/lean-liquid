-- import laurent_measures.functor
import laurent_measures.thm69
import analysis.special_functions.logb
-- import data.real.basic

/-
This files introduces the maps `Θ`, `Φ` (***and `Ψ` ???***), which are the "measurifications" of
`θ`, `ϕ` (*** and `ψ` ???***)
`laurent_measures.thm69`, they are morphisms in the right category.

We then prove in **???** that `θ_ϕ_exact` of `laurent_measures.thm69` becomes a short exact sequence
in the category **???**.
-/


noncomputable theory

universe u

namespace laurent_measures_ses

open laurent_measures pseudo_normed_group comphaus_filtered_pseudo_normed_group
  comphaus_filtered_pseudo_normed_group_hom
open_locale big_operators nnreal

section homs

parameter {p : ℝ≥0}

variables [fact(0 < p)] [fact (p < 1)]

variable {S : Fintype}


local notation `r` := @r p
local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r

variables {M₁ M₂ : Type u} [comphaus_filtered_pseudo_normed_group M₁] [comphaus_filtered_pseudo_normed_group M₂]

def cfpng_hom_add (f g : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) : (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
begin
  apply mk_of_bound (f.to_add_monoid_hom + g.to_add_monoid_hom) (f.bound.some + g.bound.some),
  intro c,
  refine ⟨_, _⟩,
  { intros x hx,
      simp only [comphaus_filtered_pseudo_normed_group_hom.coe_mk],
      simp only [add_monoid_hom.add_apply, coe_to_add_monoid_hom],
      convert pseudo_normed_group.add_mem_filtration (f.bound.some_spec hx) (g.bound.some_spec hx),
      rw add_mul, },
  let f₀ : filtration M₁ c → filtration M₂ (f.bound.some * c) := λ x, ⟨f x, f.bound.some_spec x.2⟩,
  have hf₀ : continuous f₀ := f.continuous _ (λ x, rfl),
  let g₀ : filtration M₁ c → filtration M₂ (g.bound.some * c) := λ x, ⟨g x, g.bound.some_spec x.2⟩,
  have hg₀ : continuous g₀ := g.continuous _ (λ x, rfl),
  simp only [add_monoid_hom.add_apply, coe_to_add_monoid_hom],
  haveI : fact ((f.bound.some * c + g.bound.some * c) ≤ ((f.bound.some + g.bound.some) * c) ) := fact.mk (le_of_eq (add_mul _ _ _).symm),
  let ι : filtration M₂ (f.bound.some * c + g.bound.some * c) → filtration M₂ ((f.bound.some + g.bound.some) * c) := cast_le,
  have hι : continuous ι := continuous_cast_le _ _,
  let S₀ : filtration M₂ (f.bound.some * c) × filtration M₂ (g.bound.some * c) → filtration M₂ (f.bound.some * c + g.bound.some * c) := λ x, ⟨x.fst + x.snd, add_mem_filtration x.fst.2 x.snd.2⟩,
  have hS₀ := continuous_add' (f.bound.some * c) (g.bound.some * c),
  exact hι.comp (hS₀.comp (continuous.prod_mk hf₀ hg₀)),
end

def cfpng_hom_neg (f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) : (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
begin
  apply mk_of_bound (- f.to_add_monoid_hom) (f.bound.some),
  intro c,
  refine ⟨_, _⟩,
  { intros x hx,
    simp only [comphaus_filtered_pseudo_normed_group_hom.coe_mk],
    convert pseudo_normed_group.neg_mem_filtration (f.bound.some_spec hx) },
  let f₀ : filtration M₁ c → filtration M₂ (f.bound.some * c) := λ x, ⟨f x, f.bound.some_spec x.2⟩,
  have hf₀ : continuous f₀ := f.continuous _ (λ x, rfl),
  exact (continuous_neg' _).comp hf₀,
end

instance : add_comm_group (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
{ add := cfpng_hom_add,
  add_assoc := by {intros, ext, apply add_assoc},
  zero := 0,
  zero_add := by {intros, ext, apply zero_add},
  add_zero := by {intros, ext, apply add_zero},
  neg := cfpng_hom_neg,
  add_left_neg := by {intros, ext, apply add_left_neg},
  add_comm := by {intros, ext, apply add_comm} }

variable (S)

def Φ : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S) := 2 • shift (-1) - id

variable {S}

lemma Φ_eq_ϕ (F : ℒ S) : Φ S F = ϕ F := rfl

section theta

lemma θ_zero : θ (0 : ℒ S) = 0 :=
begin
  dsimp only [θ, theta.ϑ],
  funext,
  simp only [zero_apply, int.cast_zero, zero_mul, tsum_zero, real_measures.zero_apply],
end

lemma θ_add (F G : ℒ S) : θ (F + G) = θ F + θ G :=
begin
  dsimp only [θ, theta.ϑ],
  funext,
  simp only [laurent_measures.add_apply, int.cast_add, one_div, inv_zpow', zpow_neg₀, real_measures.add_apply, tsum_add],
  rw ← tsum_add,
  { congr,
    funext,
    rw add_mul },
  all_goals {apply summable_of_summable_norm, simp_rw [normed_field.norm_mul, normed_field.norm_inv, normed_field.norm_zpow, real.norm_two, ← inv_zpow₀, inv_eq_one_div] },
  exact aux_thm69.summable_smaller_radius_norm F.d r_half (F.summable s) (lt_d_eq_zero _ _),
  exact aux_thm69.summable_smaller_radius_norm G.d r_half (G.summable s) (lt_d_eq_zero _ _),
end

--for mathlib
lemma nnreal.rpow_int_cast (x : ℝ≥0) (n : ℤ) : x ^ n = x ^ (n : ℝ) := by {
  rw [← nnreal.coe_eq, nnreal.coe_zpow, ← real.rpow_int_cast, ← nnreal.coe_rpow] }

-- lemma nnreal.mul_le_mul_left {a b c : ℝ≥0} : a * b ≤ a * c ↔ b ≤ c := sorry

-- lemma nnreal.mul_le_mul_right {a b c : ℝ≥0} : b * a ≤ c * a ↔ b ≤ c := sorry

lemma nnreal.rpow_le_rpow_of_exponent_le {x : ℝ≥0} (x1 : 1 ≤ x) {y z : ℝ}
  (hyz : y ≤ z) :
  x ^ y ≤ x ^ z :=
by { cases x with x hx, exact real.rpow_le_rpow_of_exponent_le x1 hyz }

/-  This lemma seems to need extra assumptions, e.g. `0 ≤ y`.  See example below. -/
--lemma nnreal.rpow_le_rpow_of_exponent_le (x : ℝ≥0) {y z : ℝ} (hxyz : y ≤ z) :
--  x ^ y ≤ x ^ z :=
--sorry

example : ¬ (1 / 2 : ℝ≥0) ^ (-1 : ℝ) ≤ (1 / 2) ^ 1 :=
by simp only [nnreal.rpow_neg_one, one_div, inv_inv, pow_one, nnreal.le_inv_iff_mul_le, ne.def,
    bit0_eq_zero, one_ne_zero, not_false_iff, not_le, one_lt_mul one_le_two one_lt_two]


-- lemma nnreal.rpow_le_rpow {x y: ℝ≥0} {z : ℝ} (h : x ≤ y) : x ^ z ≤ y ^ z := sorry
-- begin
--   rcases eq_or_lt_of_le h₁ with rfl|h₁', { refl },
--   rcases eq_or_lt_of_le h₂ with rfl|h₂', { simp },
--   exact le_of_lt (rpow_lt_rpow h h₁' h₂')
-- end

lemma nnreal.tsum_geom_arit_inequality (f: ℤ → ℝ) (r' : ℝ) : ∥ tsum (λ n, (f n : ℝ)) ∥₊ ^ r' ≤
  tsum (λ n, ∥ (f n)∥₊ ^ r' ) :=
begin
  sorry--asked Heather, use nnreal.rpow_sum_le_sum_rpow in `real_measures.lean`
end


lemma aux_bound (F : ℒ S) (s : S) : ∀ (b : ℤ), ∥(F s b : ℝ) ∥₊ ^ (p : ℝ) * (2⁻¹ ^ (p : ℝ)) ^ (b : ℝ) ≤
∥F s b∥₊ * r ^ b :=
begin
  intro b,
  rw [inv_eq_one_div, nnreal.rpow_int_cast],
  refine mul_le_mul_of_nonneg_right _ (real.rpow_nonneg_of_nonneg (nnreal.coe_nonneg _) _),
  have p_le_one : (p : ℝ) ≤ 1,
  { rw ← nnreal.coe_one,
    exact (nnreal.coe_lt_coe.mpr $ fact.out _).le },
  by_cases hF_nz : F s b = 0,
  { rw [hF_nz, int.cast_zero, nnnorm_zero, nnnorm_zero, nnreal.zero_rpow],
    rw [ne.def, ← nnreal.coe_zero, nnreal.coe_eq, ← ne.def],
    exact ne_of_gt (fact.out _) },
  { convert nnreal.rpow_le_rpow_of_exponent_le _ p_le_one,
    { rw nnreal.rpow_one,
      refl },
    { refine not_lt.mp (λ hf, hF_nz (int.eq_zero_iff_abs_lt_one.mp _)),
      suffices : (|F s b| : ℝ) < 1, exact_mod_cast this,
      rw ← int.norm_eq_abs,
      rwa [← nnreal.coe_lt_coe, ← nnnorm_norm, real.nnnorm_of_nonneg (norm_nonneg _)] at hf } }
end

lemma θ_bound : ∀ c : ℝ≥0, ∀ F : (ℒ S), F ∈ filtration (ℒ S) c → (θ F) ∈ filtration (ℳ S)
  (1 * c) :=
begin
  intros c F hF,
  rw mem_filtration_iff at hF,
  dsimp only [laurent_measures.has_nnnorm] at hF,
  rw [one_mul, real_measures.mem_filtration_iff],
  dsimp only [real_measures.has_nnnorm, θ, theta.ϑ],
  let T := S.2.1,
  have ineq : ∀ (s ∈ T), ∥∑' (n : ℤ), ((F s n) : ℝ) * (1 / 2) ^ n∥₊ ^ (p : ℝ) ≤ ∑' (n : ℤ),
    ∥ ((F s n) : ℝ) * (1 / 2) ^ n∥₊ ^ (p : ℝ),
  { intros s hs,
    apply nnreal.tsum_geom_arit_inequality (λ n, ((F s n) * (1 / 2) ^ n)) (p : ℝ), },
  apply (finset.sum_le_sum ineq).trans,
  simp_rw [normed_field.nnnorm_mul, ← inv_eq_one_div, normed_field.nnnorm_zpow,
    normed_field.nnnorm_inv, nnreal.mul_rpow, real.nnnorm_two, nnreal.rpow_int_cast,
    ← nnreal.rpow_mul (2 : ℝ≥0)⁻¹, mul_comm, nnreal.rpow_mul (2 : ℝ≥0)⁻¹],
  apply le_trans _ hF,
  apply finset.sum_le_sum,
  intros s hs,
  apply tsum_le_tsum,
  exact aux_bound F s,
  refine nnreal.summable_of_le _ (F.2 s),
  exacts [aux_bound F s, F.2 s],
end

lemma θ_bound' :  ∀ c : ℝ≥0, ∀ F : (ℒ S), F ∈ filtration (ℒ S) c → (θ F) ∈ filtration (ℳ S)
  c := by {simpa [one_mul] using θ_bound}

def θ_to_add : (ℒ S) →+ (ℳ S) :=
{ to_fun := λ F, θ F,
  map_zero' := θ_zero,
  map_add' := θ_add, }

-- variable (c : ℝ≥0)
-- #check filtration (ℒ S) c

-- open theta
-- #check ϑ (1/2) r p S

-- def ϑ_c (c : ℝ≥0) : (filtration (ℒ S) c) → (filtration (ℳ S) (1 * c)) :=
  --λ f, ⟨ϑ r r p S f, - ⟩
-- lemma continuous_ϑ_c (c : ℝ≥0) : continuous
-- instance : topological_space (ℳ S) :=
-- begin
--   dsimp only [real_measures],
--   apply_instance,
-- end

-- example (c : ℝ≥0) : is_open ({F | ∥ F.1 ∥₊ < c} : set (filtration (ℒ S) c)) :=


variable (S)

--**[FAE]** Useless?
-- structure box_ℒ_c (S : Fintype) (c : ℝ≥0) :=
-- (to_fun : S → ℤ → ℤ )
-- (summable' : ∀ s, summable (λ n, ∥ (to_fun s n : ℝ) ∥₊ * r ^n) )
-- (bound' : ∀ (s : S), tsum (λ n, ∥ (to_fun s n : ℝ) ∥₊ * r ^n) ≤ c)

def sbox_ℒ_c (c : ℝ≥0) := filtration (laurent_measures r (Fintype.of punit)) c
-- def sbox_ℒ_c (c : ℝ≥0) := {F : laurent_measures r (Fintype.of punit) // ∥ F ∥₊ ≤ c }
-- (to_fun : ℤ → ℤ )
-- (summable' : summable (λ n, ∥ (to_fun n : ℝ) ∥₊ * r ^n) )
-- (bound' : tsum (λ n, ∥ (to_fun n : ℝ) ∥₊ * r ^n) ≤ c)

--**[FAE]** Useless?
-- instance (c : ℝ≥0) : topological_space (box_ℒ_c  c) :=
-- begin
--   sorry,
-- end

-- example (c : ℝ≥0) : topological_space (filtration (laurent_measures r (Fintype.of punit)) c) :=
--   by refine cofinite_topology ↥(filtration (laurent_measures «r» (Fintype.of punit)) c)

instance (c : ℝ≥0) : topological_space (sbox_ℒ_c c) := by refine
  cofinite_topology ↥(filtration (laurent_measures r (Fintype.of punit)) c)
-- begin
--   unfold,
--   apply_instance,
-- end

--**[FAE]** Useless?
-- def cast_ℒ_c (c : ℝ≥0) : filtration (ℒ S) c → (box_ℒ_c S c) :=
  -- (S → {f : ℤ → ℤ // summable (λ n, ∥ (f n : ℝ) ∥₊ * r ^n) ∧ tsum (λ n, ∥ f n ∥₊ * r ^n) ≤ c}) :=
-- begin
--   intro F,
--   refine ⟨F.1, F.1.2, _⟩,
--   sorry,
-- end

def scast_ℒ_c (c : ℝ≥0) (s : S) : filtration (ℒ S) c → (sbox_ℒ_c c) :=
  -- (S → {f : ℤ → ℤ // summable (λ n, ∥ (f n : ℝ) ∥₊ * r ^n) ∧ tsum (λ n, ∥ f n ∥₊ * r ^n) ≤ c}) :=
begin
  intro F,
  refine ⟨⟨(λ _, F.1 s), (λ _, F.1.2 s)⟩, _⟩,
  sorry,
end

--**[FAE]** Useless?
-- lemma cont_cast_ℒ (c : ℝ≥0) : continuous (cast_ℒ_c c S:) := sorry
-- lemma cont_cast_ℒ (c : ℝ≥0) : continuous ((cast_ℒ_c c) : filtration (ℒ S) c →  (box_ℒ_c S c)) := sorry

lemma cont_scast_ℒ (c : ℝ≥0) (s : S) : continuous (scast_ℒ_c S c s) := sorry
-- lemma cont_scast_ℒ (c : ℝ≥0) (s : S) : continuous ((scast_ℒ_c c s) : filtration (ℒ S) c →  (sbox_ℒ_c c)) := sorry

def cast_ℳ_c (c : ℝ≥0) : filtration (ℳ S) c →
  (filtration (real_measures p (Fintype.of punit)) c) :=
begin
  sorry,
  -- intros F s,
  -- refine ⟨F.1 s, _⟩,
  -- sorry,
end

--**[FAE]** Useless?
-- def cast_ℳ_c_at_s (c : ℝ≥0) (s : S) : filtration (real_measures p S) (1 * c) →
--   {x : ℝ // ∥ x ∥ ^ (p : ℝ) ≤ c} := (λ F, cast_ℳ_c c F s)

--**[FAE]** Useless?
-- lemma cont_at_cast_ℳ (c : ℝ≥0) {X : Type*} [topological_space X] (f : X → filtration (ℳ S) (1 * c)) :
--   continuous (cast_ℳ_c c ∘ f) → continuous f := sorry

--**[FAE]** Useless?
-- lemma aux3' (c : ℝ≥0) {X : Type*} (s : S) [topological_space X] {f : X → filtration (ℳ S) (1 * c)} :
--   continuous f ↔ continuous (cast_ℳ_c_at_s c s ∘ f) := sorry

open metric

lemma cont_iff_for_all_closed (c : ℝ≥0) {X : Type*} [topological_space X]
  (f : X → closed_ball (0 : ℝ) c) (H : ∀ a : ℝ≥0, ∀ (H : a ≤ c), is_closed
    (f⁻¹' ((closed_ball ⟨(0 : ℝ), (mem_closed_ball_self c.2)⟩ a) : set ((closed_ball (0 : ℝ) c)))))
    : continuous f :=
 begin
   sorry,
 end

--**[FAE]** Useless?
-- lemma aux5 (c : ℝ≥0) : continuous (coe ∘ (θ_c S c) : (filtration (ℒ S) c) → (ℳ S)) :=
-- begin
--   rw continuous_pi_iff,
--   intro s,
--   -- apply (aux4 c).mpr,
--   rw continuous_iff_is_closed,
--   intros K hK,
--   sorry,
-- end

def equiv_ball_ℓp (c : ℝ≥0) : {x : ℝ // ∥ x ∥ ^ (p : ℝ) ≤ c} ≃ₜ
  closed_ball (0 : ℝ) (c ^ (1 / p : ℝ)) :=
begin
  fconstructor,
  {fconstructor,
    { intro x,
      use x,
      rw mem_closed_ball_zero_iff,
      sorry,

    },
  {sorry, },
  {sorry, },
  { sorry, },
  },
  sorry,
  sorry,
end


def θ_c (c : ℝ≥0) (T : Fintype) : (filtration (laurent_measures r T) c) →
  (filtration (real_measures p T) c) :=
begin
  intro f,
  rw [← one_mul c],
  use ⟨θ f, θ_bound c f f.2⟩,
end
-- λ f, ⟨θ f, θ_bound c f f.2⟩


--**[FAE]** Useless?
-- def θ'_c (c : ℝ≥0) : (box_ℒ_c S c) → (S → {x : ℝ // ∥ x ∥ ^ (p : ℝ) ≤ c}) := sorry
-- def θ'_c (c : ℝ≥0) : (S → {f : ℤ → ℤ // summable (λ n, ∥ (f n : ℝ) ∥₊ * r ^n) ∧
--   tsum (λ n, ∥ f n ∥₊ * r ^n) ≤ c}) → (S → {x : ℝ // ∥ x ∥ ^ (p : ℝ) ≤ c}) := sorry

-- lemma aux_commutative_θ (c : ℝ≥0) : (cast_ℳ_c c) ∘ (θ_c S c) = (θ'_c S c) ∘ (cast_ℒ_c c) := sorry

-- lemma aux_commutative_pr (c : ℝ≥0) (s : S) : (cast_ℳ_c c) ∘ (θ_c S c) = (θ'_c S c) ∘ (cast_ℒ_c c) := sorry

-- variables (a c : ℝ≥0)
-- variable (s : S)
-- variable (t : sbox_ℒ_c c)
-- #check (θ_c c (Fintype.of punit)) ∘ (scast_ℒ_c S c s)
-- #check sbox_ℒ_c c
-- #check theta.ϑ₀ (1 / 2 ) r (t.1)
-- #check θ_c c
-- #check (cast_ℳ_c S c) ∘ (θ_c c S)

--**[FAE]** Almost OK: ϑ₀ still lands in ℝ instead of in the small box, but otherwise it is OK
lemma saux_commutative_pr (c : ℝ≥0) (s : S) (F : filtration (ℒ S) c):
  -- (cast_ℳ_c S c (θ_c c S F) s) = (θ_c c (Fintype.of punit)) (scast_ℒ_c S c s F) :=
  (θ_c c (Fintype.of punit)) ∘ (scast_ℒ_c S c s) = (cast_ℳ_c S c) ∘ (θ_c c S) :=
begin
  sorry,
end

-- lemma aux_6 (a c : ℝ≥0) (s : S) (ha : a ≤ c ^ (1 / p : ℝ)): ((equiv_ball_ℓp c) ∘
--   (λ F, (cast_ℳ_c c (θ_c S c F) s)))⁻¹'
--   (closed_ball ⟨(0 : ℝ), (mem_closed_ball_self (a.2.trans ha))⟩ a) = ∅ :=
-- begin
--   sorry,
-- end


theorem continuous_θ_c (c : ℝ≥0) : continuous (θ_c c S) :=
begin
  sorry,




  -- dsimp only [θ_c],
  -- apply cont_at_cast_ℳ c (θ_c S c),
  -- rw aux_commutative_θ,
  -- apply continuous.comp _ (cont_cast_ℒ c),
  -- apply continuous_pi,
  -- intro s,
  -- sorry,







  --**[FAE]** Old version
  -- sorry;
  -- {
  -- dsimp only [θ_c],
  -- apply cont_at_cast_ℳ c (θ_c S c),
  -- apply continuous_pi,
  -- intro s,
  -- apply ((equiv_ball_ℓp c).comp_continuous_iff).mp,
  -- let f := (equiv_ball_ℓp c) ∘ (λ a,
  --   (cast_ℳ_c c ∘ θ_c S c) a s),
  -- apply cont_at_closed (c ^ (1 / p : ℝ)) f,
  -- intros a ha,
  -- dsimp [f],
  -- --from here, it is clearly broken
  -- convert is_closed_empty,
  -- apply aux_6 S a c s ha,
  -- }
  -- unfold,
  -- dsimp [f, cast_ℳ_c, θ_c],

  -- sorry,



  --all_goals {apply_instance},
end


def Θ : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℳ S) :=
mk_of_strict (θ_to_add)
begin
  intro c,
  use θ_bound' c,
  convert continuous_θ_c S c,
  simp only [θ_c, one_mul, eq_mpr_eq_cast, set_coe_cast],
  refl,
end

variable {S}

end theta

end homs

end laurent_measures_ses
