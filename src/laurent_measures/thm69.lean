import for_mathlib.short_exact_sequence
import laurent_measures.basic
import laurent_measures.theta


namespace thm_69

open category_theory category_theory.limits theta laurent_measures
open_locale nnreal classical big_operators


universe u
variable (ξ : ℝ)
variables (r : ℝ≥0) [fact (0 < r)]

noncomputable theory

instance (S : Fintype) : has_scalar (laurent_measures r (Fintype.of punit)) (laurent_measures r S) :=
{ smul := sorry}

section SES_thm69

local notation `ℳ` := real_measures
local notation `𝑓` := (ker_generator ξ r)
variable (S : Fintype)
variables (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] [fact ((ξ : ℝ) ^ (p : ℝ) = r)]

include ξ r

/-- This `to_meas_θ` is the "measurification" of the map `θ` of
Theorem 6.9. Thus, `to_meas_θ` is the map inducing the isomorphism of Theorem 6.9 (2)-/
def to_meas_θ : laurent_measures r S → ℳ p S :=
λ F s, θ ξ r ⟨(λ _, F s), (λ _, F.2 s)⟩

lemma to_meas_θ_zero :
 (to_meas_θ ξ r S p (0 : laurent_measures r S)) = 0 := sorry

lemma to_meas_θ_add (F G : laurent_measures r S) :
 (to_meas_θ ξ r S p (F + G)) = (to_meas_θ ξ r S p F) + (to_meas_θ ξ r S p G) := sorry

/--This `lemma to_meas_θ_bound` is precisely Prop 7.2 (3) of `Analytic.pdf`-/
lemma to_meas_θ_bound : ∃ (C : ℝ≥0), ∀ (c : ℝ≥0) (F : laurent_measures r S),
  ∥ F ∥ ≤ c → ∥ to_meas_θ ξ r S p F ∥₊ ≤ C * c := sorry

def to_add_hom_meas_θ : add_hom (laurent_measures r S) (ℳ p S) :=
add_monoid_hom.mk' (λ F, to_meas_θ ξ r S p F)
begin
    intros a b,
    have := to_meas_θ_add ξ r S p a b,
    exact this,
  end

def Θ : comphaus_filtered_pseudo_normed_group_hom (laurent_measures r S) (ℳ p S) :=
  { to_fun := to_meas_θ ξ r S p,
    bound' := to_meas_θ_bound ξ r S p,
    continuous' := sorry, -- [FAE] I guess that this is Prop 7.2 (4) of `Analytic.pdf`
    -- .. to_add_hom_meas_θ ξ r S p,
    map_add' := (to_add_hom_meas_θ ξ r S p).2,
    map_zero' := sorry }


lemma chain_complex_thm69 (F : laurent_measures r S) : Θ ξ r S p (𝑓 • F) = 0 :=
begin
  funext s,
  sorry,
  -- simp only [real_measures.zero_apply],
  -- dsimp [Θ],
  -- dsimp [to_meas_θ],
  -- dsimp [θ],
  -- dsimp [has_scalar],
  -- rw pi.has_scalar,
end


/-
From here onwards, the bundled version
-/
variable [imCHFPNG : has_images (CompHausFiltPseuNormGrp.{u})]
variable [zerCHFPNG : has_zero_morphisms (CompHausFiltPseuNormGrp.{u})]
variable [kerCHFPNG : has_kernels (CompHausFiltPseuNormGrp.{u})]



def SES_thm69 (S : Fintype) : @category_theory.short_exact_sequence CompHausFiltPseuNormGrp.{u} _
  imCHFPNG zerCHFPNG kerCHFPNG :=
{ fst := bundled.of (laurent_measures r S),
  snd := bundled.of (laurent_measures r S),
  trd := bundled.of (ℳ p S),
  f :=
  begin
    let φ := λ (F : laurent_measures r S), (ker_generator ξ r) • F,
    use φ,
    sorry,
    sorry,
    sorry,
    sorry,-- [FAE] These four are the properties that the scalar multiplication by a measure on the
    --singleton (as endomorphism of S-measures) must satisfy
  end,
  g := @Θ ξ r _ S p _ _ _,
  mono' := sorry,
  epi' := sorry,
  exact' := sorry }

end SES_thm69

end thm_69
