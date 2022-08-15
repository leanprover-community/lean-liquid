import Radon.setup

open_locale nnreal big_operators classical

noncomputable theory

open category_theory
open category_theory.limits
open topological_space

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space

namespace Profinite

/--
The space of signed `p`-Radon measures on `X`, bounded by `c`.
-/
@[derive topological_space]
def Radon (X : Profinite.{0}) (p c : ℝ≥0) :
  Top.{0} :=
Top.of { μ : weak_dual ℝ C(X,ℝ) // μ.bdd p c }

/--
The space of signed `p`-Radon measures on `X`, bounded by `c`.
This is a variant of `Radon` which uses the dual of locally constant functions
as opposed to continuous functions, to be used an an auxiliary declaration in the
constructions below.
-/
@[derive topological_space]
def Radon_LC (X : Profinite.{0}) (p c : ℝ≥0) :
  Top.{0} :=
Top.of { μ : weak_dual ℝ (locally_constant X ℝ) // μ.bdd_LC p c }

/--
A continuous map `X → Y` induces a map between spaces of `p`-Radon measures
with a given bound.
-/
def map_Radon {X Y : Profinite.{0}} (f : X ⟶ Y)
  (p c : ℝ≥0) [fact (0 < p)] :
  X.Radon p c ⟶ Y.Radon p c :=
{ to_fun := λ μ, ⟨weak_dual.comap f.comap μ.1,
    weak_dual.bdd_comap _ μ.2 _⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    exact continuous_linear_map.continuous _,
  end }

/--
A continuous map `X → Y` induces a map between spaces of `p`-Radon measures
with a given bound. (This is the locally constant variant.)
-/
def map_Radon_LC {X Y : Profinite.{0}} (f : X ⟶ Y)
  (p c : ℝ≥0) [fact (0 < p)] :
  X.Radon_LC p c ⟶ Y.Radon_LC p c :=
{ to_fun := λ μ, ⟨weak_dual.comap f.comap_LC μ.1,
    weak_dual.bdd_LC_comap _ μ.2 _⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    exact continuous_linear_map.continuous _,
  end }

/--
The functor sending a topological space to the space of `p`-Radon
measures bounded by `c`.
-/
def Radon_functor (p c : ℝ≥0) [fact (0 < p)] :
  Profinite.{0} ⥤ Top.{0} :=
{ obj := λ X, X.Radon p c,
  map := λ X Y f, map_Radon f _ _,
  map_id' := λ X, by { ext, dsimp [map_Radon, weak_dual.comap], congr' 1,
    ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

/--
The functor sending a topological space to the space of `p`-Radon
measures bounded by `c`. This is the locally constant variant.
-/
def Radon_LC_functor (p c : ℝ≥0) [fact (0 < p)] :
  Profinite.{0} ⥤ Top.{0} :=
{ obj := λ X, X.Radon_LC p c,
  map := λ X Y f, map_Radon_LC f _ _,
  map_id' := λ X,
    by { ext, dsimp [map_Radon_LC, weak_dual.comap], congr' 1, ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

.


/--
An auxiliary definition to be used in the constructions below.
-/
def weak_dual_C_to_LC (X : Profinite.{0}) :
  weak_dual ℝ C(X,ℝ) →L[ℝ] weak_dual ℝ (locally_constant X ℝ) :=
weak_dual.comap $ lc_to_c _

lemma dense_range_coe₂ (X : Profinite.{0}) :
  dense_range (λ p : locally_constant X ℝ × locally_constant X ℝ,
    (lc_to_c X p.1, lc_to_c X p.2)) :=
begin
  letI : uniform_space (locally_constant.pkg X ℝ).space :=
    (locally_constant.pkg X ℝ).uniform_struct,
  exact (locally_constant.pkg X ℝ).dense.prod_map (locally_constant.pkg X ℝ).dense
end

/--
An auxiliary definition to be used in the constructions below.
-/
def weak_dual_LC_to_C (X : Profinite.{0}) :
  weak_dual ℝ (locally_constant X ℝ) →ₗ[ℝ] weak_dual ℝ C(X,ℝ) :=
{ to_fun := λ f,
  { to_fun := (locally_constant.pkg X ℝ).extend f,
    map_add' := begin
      letI : uniform_space (locally_constant.pkg X ℝ).space :=
        (locally_constant.pkg X ℝ).uniform_struct,
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
    map_smul' := begin
      letI : uniform_space (locally_constant.pkg X ℝ).space :=
        (locally_constant.pkg X ℝ).uniform_struct,
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
  map_add' := begin
    letI : uniform_space (locally_constant.pkg X ℝ).space :=
      (locally_constant.pkg X ℝ).uniform_struct,
    intros f g, ext ff, dsimp,
    apply (locally_constant.pkg X ℝ).induction_on ff,
    { apply is_closed_eq,
      apply (locally_constant.pkg X ℝ).continuous_extend, apply_instance,
      let G : C(X,ℝ) → ℝ × ℝ := λ ff,
        ((locally_constant.pkg X ℝ).extend f ff, (locally_constant.pkg X ℝ).extend g ff),
      change continuous ((λ a : ℝ × ℝ, a.1 + a.2) ∘ G),
      refine continuous.comp continuous_add _,
      apply continuous.prod_mk,
      apply (locally_constant.pkg X ℝ).continuous_extend, apply_instance,
      apply (locally_constant.pkg X ℝ).continuous_extend, apply_instance },
    { intros a,
      rw [(locally_constant.pkg X ℝ).extend_coe],
      rw [(locally_constant.pkg X ℝ).extend_coe],
      rw [(locally_constant.pkg X ℝ).extend_coe],
      refl,
      any_goals { apply continuous_linear_map.uniform_continuous },
      any_goals { apply_instance } },
  end,
  map_smul' := begin
    letI : uniform_space (locally_constant.pkg X ℝ).space :=
      (locally_constant.pkg X ℝ).uniform_struct,
    intros r f, ext ff, dsimp,
    apply (locally_constant.pkg X ℝ).induction_on ff,
    { apply is_closed_eq,
      apply (locally_constant.pkg X ℝ).continuous_extend, apply_instance,
      refine continuous.comp (continuous_mul_left r) _,
      apply (locally_constant.pkg X ℝ).continuous_extend, apply_instance },
    { intros a,
      rw [(locally_constant.pkg X ℝ).extend_coe],
      rw [(locally_constant.pkg X ℝ).extend_coe],
      refl,
      any_goals { apply_instance },
      exact f.uniform_continuous,
      exact (r • f).uniform_continuous },
  end }

end Profinite
