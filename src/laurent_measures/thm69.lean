import for_mathlib.short_exact_sequence
import laurent_measures.basic
import laurent_measures.theta


namespace thm_69

open category_theory category_theory.limits theta laurent_measures
open_locale nnreal classical big_operators


universe u
variable (ξ : ℝ)
variables {r : ℝ≥0} [fact (0 < r)]

noncomputable theory

instance (S : Fintype) : has_scalar (laurent_measures r (Fintype.of punit)) (laurent_measures r S) :=
{ smul :=
  begin
    intros f G,
    constructor,
    intro s,
    sorry,
    intros s n,
    use (f punit.star n) * (G s n),
  end }

section SES_thm69

local notation `ℳ` := real_measures
variable (S : Fintype)
variables (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] [fact ((ξ : ℝ) ^ (p : ℝ) = r)]

/-- This `to_meas_θ` is the "measurification" of the map `θ` of
Theorem 6.9. Thus, `to_meas_θ` is the map inducing the isomorphism of Theorem 6.9 (2)-/
def to_meas_θ : laurent_measures r S → ℳ p S :=
λ F s, θ ξ r ⟨(λ _, F s), (λ _, F.2 s)⟩

lemma to_meas_θ_zero :
 (to_meas_θ ξ S p (0 : laurent_measures r S)) = 0 := sorry

lemma to_meas_θ_add (F G : laurent_measures r S) :
 (to_meas_θ ξ S p (F + G)) = (to_meas_θ ξ S p F) + (to_meas_θ ξ S p G) := sorry

/--This `lemma to_meas_θ_cont` is precisely Prop 7.2 (3) of `Analytic.pdf`-/
lemma to_meas_θ_cont : ∃ (C : ℝ≥0), ∀ (c : ℝ≥0) (F : laurent_measures r S),
  ∥ F ∥ ≤ c → ∥ to_meas_θ ξ S p F ∥₊ ≤ C * c := sorry

def Θ : comphaus_filtered_pseudo_normed_group_hom (laurent_measures r S) (ℳ p S) :=
{ to_fun := to_meas_θ ξ S p,
  map_zero' := to_meas_θ_zero ξ S p,
  map_add' := to_meas_θ_add ξ S p,
  bound' := by {simp_rw [pseudo_normed_group.filtration, (laurent_measures.norm_def)],
    apply to_meas_θ_cont},
  continuous' := sorry } -- [FAE] I guess that this is Prop 7.2 (4) of `Analytic.pdf`

--[FAE] Don't we already know that CompHausFiltPseuNormGrp is "nice"?
variable [imCHFPNG : has_images (CompHausFiltPseuNormGrp.{u})]
variable [zerCHFPNG : has_zero_morphisms (CompHausFiltPseuNormGrp.{u})]
variable [kerCHFPNG : has_kernels (CompHausFiltPseuNormGrp.{u})]


-- variables (S : Fintype) (F : laurent_measures r S)
-- #check (ker_generator ξ r) • F

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
