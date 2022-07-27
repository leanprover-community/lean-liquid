import challenge
import topology.algebra.module.weak_dual

variables (X : Profinite.{0})

noncomputable theory

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space

-- The abstract completion package exhibiting `C(X,ℝ)` as the completion of `LC(X,ℝ)`.
example : abstract_completion (locally_constant X ℝ) := locally_constant.pkg X ℝ

example : (locally_constant.pkg X ℝ).space = C(X,ℝ) := rfl
example : (locally_constant.pkg X ℝ).coe = locally_constant.to_continuous_map := rfl

example (f : locally_constant X ℝ →L[ℝ] ℝ) : uniform_continuous f :=
begin
  apply uniform_continuous_of_tendsto_zero,
  simpa using f.continuous.tendsto 0,
end

abbreviation signed_Radon_measure := weak_dual ℝ C(X,ℝ)

def lc_to_c : locally_constant X ℝ →L[ℝ] C(X,ℝ) :=
{ to_fun := locally_constant.to_continuous_map,
  map_add' := λ f g, rfl,
  map_smul' := λ a f, rfl,
  cont := (locally_constant.pkg X ℝ).continuous_coe } -- ;-)

def signed_Radon_measure.comparison :
  signed_Radon_measure X →L[ℝ] weak_dual ℝ (locally_constant X ℝ) :=
{ to_fun := λ f, f.comp (lc_to_c _),
  map_add' := λ f g, rfl,
  map_smul' := λ a f, rfl,
  cont := sorry }

def signed_Radon_measure.inverse :
  weak_dual ℝ (locally_constant X ℝ) →L[ℝ] signed_Radon_measure X :=
{ to_fun := λ f,
  { to_fun := (locally_constant.pkg X ℝ).extend f,
    map_add' := sorry,
    map_smul' := sorry,
    cont := (locally_constant.pkg X ℝ).continuous_extend },
  map_add' := sorry,
  map_smul' := sorry,
  cont := sorry }

def signed_Radon_measure.equiv :
   signed_Radon_measure X ≃L[ℝ] weak_dual ℝ (locally_constant X ℝ) :=
{ inv_fun := signed_Radon_measure.inverse _,
  left_inv := sorry,
  right_inv := sorry,
  continuous_to_fun := (signed_Radon_measure.comparison X).cont,
  continuous_inv_fun := (signed_Radon_measure.inverse X).cont,
  ..(signed_Radon_measure.comparison X) }
