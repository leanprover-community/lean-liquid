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
  cont := begin
    apply weak_dual.continuous_of_continuous_eval,
    intro f,
    apply weak_dual.eval_continuous (lc_to_c X f),
  end }

local attribute [instance] abstract_completion.uniform_struct

-- generalize this to arbitrary abstract completions:
lemma dense_range_coe₂ :
  dense_range (λ p : locally_constant X ℝ × locally_constant X ℝ, (lc_to_c X p.1, lc_to_c X p.2)) :=
(locally_constant.pkg X ℝ).dense.prod_map (locally_constant.pkg X ℝ).dense

def signed_Radon_measure.inverse :
  C(weak_dual ℝ (locally_constant X ℝ), signed_Radon_measure X) :=
{ to_fun := λ f,
  { to_fun := (locally_constant.pkg X ℝ).extend f,
    map_add' := by sorry; begin
      letI : add_group (locally_constant.pkg X ℝ).space :=
        continuous_map.add_group,
      letI : topological_add_group (locally_constant.pkg X ℝ).space :=
        continuous_map.topological_add_group,
      rw ← prod.forall',
      refine is_closed_property (dense_range_coe₂ X) _ _,
      { apply is_closed_eq,
        { refine (locally_constant.pkg X ℝ).continuous_extend.comp continuous_add },
        { refine continuous.add _ _;
          refine (locally_constant.pkg X ℝ).continuous_extend.comp _,
          exact continuous_fst,
          exact continuous_snd } },
      { rintro ⟨φ, ψ⟩, dsimp only,
        have hf := continuous_linear_map.uniform_continuous f,
        rw [← (lc_to_c X).map_add],
        erw [(locally_constant.pkg X ℝ).extend_coe hf, (locally_constant.pkg X ℝ).extend_coe hf,
          (locally_constant.pkg X ℝ).extend_coe hf, map_add], }
    end,
    map_smul' := by sorry; begin
      letI : add_group (locally_constant.pkg X ℝ).space :=
        continuous_map.add_group,
      letI : topological_add_group (locally_constant.pkg X ℝ).space :=
        continuous_map.topological_add_group,
      letI : has_smul ℝ (locally_constant.pkg X ℝ).space :=
        continuous_map.has_smul,
      letI : has_continuous_smul ℝ (locally_constant.pkg X ℝ).space :=
        continuous_map.has_continuous_smul,
      intros r φ,
      apply (locally_constant.pkg X ℝ).induction_on φ; clear φ,
      { apply is_closed_eq,
        { refine (locally_constant.pkg X ℝ).continuous_extend.comp
            (continuous_const.smul continuous_id), },
        { refine continuous_const.smul (locally_constant.pkg X ℝ).continuous_extend } },
      { intro φ,
        have hf := continuous_linear_map.uniform_continuous f,
        erw [← (lc_to_c X).map_smul, (locally_constant.pkg X ℝ).extend_coe hf,
          (locally_constant.pkg X ℝ).extend_coe hf, map_smul],
        refl }
    end,
    cont := (locally_constant.pkg X ℝ).continuous_extend },
  continuous_to_fun := begin
    apply weak_dual.continuous_of_continuous_eval,
    intro f,
    dsimp,
    sorry
    -- apply (locally_constant.pkg X ℝ).induction_on f; clear f,
    -- { sorry, },
    -- { sorry }
  end }

def signed_Radon_measure.equiv :
   signed_Radon_measure X ≃L[ℝ] weak_dual ℝ (locally_constant X ℝ) :=
{ inv_fun := signed_Radon_measure.inverse _,
  left_inv := begin
    intro μ, ext1 f,
    change (locally_constant.pkg X ℝ).extend (μ ∘ (lc_to_c X)) f = μ f,
    apply (locally_constant.pkg X ℝ).induction_on f; clear f,
    { apply is_closed_eq,
      { exact (locally_constant.pkg X ℝ).continuous_extend },
      { exact continuous_linear_map.continuous μ } },
    { intro f,
      have aux : uniform_continuous (μ ∘ (lc_to_c X)) :=
        (continuous_linear_map.uniform_continuous μ).comp (lc_to_c X).uniform_continuous,
      rw [(locally_constant.pkg X ℝ).extend_coe aux],
      refl }
  end,
  right_inv := begin
    intro μ, ext1 f,
    show (locally_constant.pkg X ℝ).extend μ (lc_to_c X f) = μ f,
    have hμ := continuous_linear_map.uniform_continuous μ,
    erw [(locally_constant.pkg X ℝ).extend_coe hμ],
  end,
  continuous_to_fun := (signed_Radon_measure.comparison X).cont,
  continuous_inv_fun := (signed_Radon_measure.inverse X).continuous,
  ..(signed_Radon_measure.comparison X) }
