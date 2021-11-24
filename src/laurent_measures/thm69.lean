-- import for_mathlib.short_exact_sequence
import laurent_measures.basic
import laurent_measures.theta
import linear_algebra.basic


namespace thm_69

-- open category_theory category_theory.limits
open theta laurent_measures
open_locale nnreal classical big_operators


-- universe u
variables (p : ℝ≥0) [fact (0 < p)] [fact (p < 1)]
variables (r : ℝ≥0) [fact (0 < r)] [fact (r < 1)]
-- variables (r : ℝ≥0) [fact ((1 / 2 : ℝ) ^ p.1 = r)]

lemma r_pos : 0 < r ∧ r < 1 := sorry

lemma r_one : r < 1 := sorry

lemma half_ineq : (1 / 2 : ℝ) < r :=
begin
  sorry,
end

noncomputable theory

-- instance (S : Fintype) : has_scalar (laurent_measures r (Fintype.of punit)) (laurent_measures r S) :=
-- { smul := sorry}


section ker_theta_half
-- open submodule linear_map

def θₗ : (laurent_measures r (Fintype.of punit)) →ₗ[ℤ] ℝ :=
{ to_fun := λ F, tsum (λ n, (F punit.star n) * (1 / 2 : ℝ) ^ n),
  map_add' :=
   begin
    intros F G,
    rw ← tsum_add,
    apply tsum_congr,
    intro m,
    rw [← add_mul, mul_eq_mul_right_iff],
    apply or.intro_left,
    rw [← int.cast_add, int.cast_inj],
    apply laurent_measures.add_apply,
    sorry, sorry,
  end,
  map_smul' := sorry }

-- lemma θ_is_linear (ξ : ℝ) : is_linear_map ℤ (θ ξ r) := sorry

-- noncomputable def θ₂.to_linear : (laurent_measures r (Fintype.of punit)) →ₗ[ℤ] ℝ :=
-- { to_fun := θ (1 / 2) r,
--   map_add' := (θ_is_linear r (1 / 2)).1,
--   map_smul' := (θ_is_linear r (1 / 2) ).2 }

-- lemma ker_θ₂_principal : submodule.is_principal ((θₗ r).ker) :=
-- begin
--   -- constructor,
--   let pos : ℕ → ℤ := λ n, (if n = 0 then -1 else if n = 1 then 2 else 0),
--   let f₀ : ℤ → ℤ := λ d : ℤ, int.rec_on d (pos) (λ n, 0),
--   use (λ s, f₀),
--   sorry,
--   ext,
--   split,
--   swap,
--   intro h_x,
--   sorry,
--   -- sorry,
--   obtain ⟨a, h_ax⟩ := mem_span_singleton.mp h_x,
--   apply mem_ker.mpr,
--   rw ← h_ax,
--   simp,
--   apply or.intro_right,
--   -- rw θₗ,
-- --   rw θ₂.to_linear,
-- --   -- rw θ.to_linear,
--   -- simp,
-- --   rw θ,
-- --   simp,
-- --   simp_rw [laurent_measures.to_Rfct],
-- --   let S : finset ℤ := {0, 1},
-- --   have hf : function.support f₀ ⊆ S, sorry,
-- --   have hf₀ : ∀ s ∉ S, ((f₀ s) : ℝ) * ((2 ^ s) : ℝ)⁻¹ = (0 : ℝ), sorry,
-- --   rw [tsum_eq_sum hf₀],
-- --   -- rw ← [has_sum_subtype_iff_of_support_subset hf],
-- --   sorry, sorry,
-- end

def ker_θₗ_generator : (laurent_measures r (Fintype.of punit)) :=
begin
  let f₀ : ℕ → ℤ := λ n, (if n = 0 then -1 else if n = 1 then 2 else 0),
  let f : ℤ → ℤ := λ d : ℤ, int.rec_on d (f₀) (λ n, 0),
  use λ _ : (Fintype.of punit), f,
  intro s,
  let A : finset ℤ := {0, 1},
  have hf : ∀ a ∉ A, ∥(f a)∥ * ((r ^ a) : ℝ) = (0 : ℝ),
  { intros a ha,
    suffices : f a = 0, by {simp only [this, norm_zero, zero_mul, implies_true_iff,
      eq_self_iff_true]},
    cases a,
    { have H : a ≠ 0 ∧ a ≠ 1,
      { dsimp only [A] at ha,
        have := (not_iff_not.mpr (@finset.mem_insert _ _ ↑a 0 {1})).mp ha,
        rw [decidable.not_or_iff_and_not, finset.mem_singleton] at this,
        tauto },
      dsimp only [f, f₀],
      rw [if_neg H.1, if_neg H.2] },
    simp only [eq_self_iff_true] },
  apply summable_of_ne_finset_zero hf,
end

local notation `𝑓` := (ker_θₗ_generator r)

variable (s : Fintype.of punit)

lemma aux₁ (s : Fintype.of punit) : function.support (𝑓 s) = {0, 1} := sorry

-- lemma ker_principal' (g : laurent_measures r (Fintype.of punit)) (hz_g : θₗ r g = 0) :
--   g ∈ ((submodule.span ℤ {𝑓}) : (submodule ℤ (laurent_measures r (Fintype.of punit)))) :=
-- begin
--   sorry,
-- end

lemma gen_mem_kernel : θₗ r 𝑓 = 0 :=
begin
  dsimp only [θₗ],
  simp only [one_div, zpow_neg₀, linear_map.coe_mk, inv_zpow'],
  dsimp only [ker_θₗ_generator],
  sorry,
end

-- lemma ker_principal : (θₗ r).ker = ℤ · 𝑓 :=
-- lemma ker_principal : (θₗ r).ker = submodule.span ℤ { 𝑓 } :=
-- begin
--   ext g,
--   split,
--   rw submodule.mem_span_singleton,sorry,
--   simp only [linear_map.mem_ker],
--   rw submodule.mem_span_singleton,
-- end

/- [FAE] The following lemma needs that `(laurent_measures r (Fintype.of punit))` have a `mul`; but
I don't know if the lemma is actually needed -/
-- lemma ker_generator_non_zerodivisor : is_regular (ker_generator ξ) :=

end ker_theta_half

section SES_thm69

local notation `ℳ` := real_measures

variable (S : Fintype)
-- variables (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] [fact ((1/2 : ℝ) ^ (p : ℝ) = r)]

include r

/-- This `θ₂` is the "measurification" of the map `θₗ` of
Theorem 6.9. Thus, `to_meas_θ` is the map inducing the isomorphism of Theorem 6.9 (2)-/
def θ₂ : laurent_measures r S → ℳ p S :=
λ F s, θₗ r ⟨(λ _, F s), (λ _, F.2 s)⟩

lemma θ₂_zero :
 (θ₂ p r S (0 : laurent_measures r S)) = 0 := sorry

lemma θ₂_add (F G : laurent_measures r S) :
 (θ₂ p r S (F + G)) = (θ₂ p r S F) + (θ₂ p r S G) := sorry

/--This `lemma to_meas_θ_bound` is precisely Prop 7.2 (3) of `Analytic.pdf`-/
lemma θ₂_bound : ∃ (C : ℝ≥0), ∀ (c : ℝ≥0) (F : laurent_measures r S),
  ∥ F ∥ ≤ c → ∥ θ₂ p r S F ∥₊ ≤ C * c := sorry

def to_add_hom_θ₂ : add_hom (laurent_measures r S) (ℳ p S) :=
add_monoid_hom.mk' (λ F, θ₂ p r S F)
begin
    intros a b,
    have := θ₂_add p r S a b,
    exact this,
  end

def Θ : comphaus_filtered_pseudo_normed_group_hom (laurent_measures r S) (ℳ p S) :=
  { to_fun := θ₂ p r S,
    bound' := θ₂_bound p r S,
    continuous' := sorry, -- [FAE] I guess that this is Prop 7.2 (4) of `Analytic.pdf`
    -- .. to_add_hom_meas_θ ξ r S p,
    map_add' := (to_add_hom_θ₂ p r S).2,
    map_zero' := sorry }


-- lemma chain_complex_thm69 (F : laurent_measures r S) : Θ p r S (𝑓 • F) = 0 :=
-- begin
--   funext s,
--   sorry,
--   -- simp only [real_measures.zero_apply],
--   -- dsimp [Θ],
--   -- dsimp [to_meas_θ],
--   -- dsimp [θ],
--   -- dsimp [has_scalar],
--   -- rw pi.has_scalar,
-- end


/-
From here onwards, the bundled version
-/
-- variable [imCHFPNG : has_images (CompHausFiltPseuNormGrp.{u})]
-- variable [zerCHFPNG : has_zero_morphisms (CompHausFiltPseuNormGrp.{u})]
-- variable [kerCHFPNG : has_kernels (CompHausFiltPseuNormGrp.{u})]



-- def SES_thm69 (S : Fintype) : @category_theory.short_exact_sequence CompHausFiltPseuNormGrp.{u} _
--   imCHFPNG zerCHFPNG kerCHFPNG :=
-- { fst := bundled.of (laurent_measures r S),
--   snd := bundled.of (laurent_measures r S),
--   trd := bundled.of (ℳ p S),
--   f :=
--   begin
--     let φ := λ (F : laurent_measures r S), (ker_θ₂_generator r) • F,
--     use φ,
--     sorry,
--     sorry,
--     sorry,
--     sorry,-- [FAE] These four are the properties that the scalar multiplication by a measure on the
--     --singleton (as endomorphism of S-measures) must satisfy
--   end,
--   g := @Θ r _ S p _ _ _,
--   mono' := sorry,
--   epi' := sorry,
--   exact' := sorry }

end SES_thm69

end thm_69
