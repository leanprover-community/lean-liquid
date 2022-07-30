import challenge
import topology.algebra.module.weak_dual
import topology.sets.closeds

open_locale nnreal big_operators
namespace Profinite

variable (X : Profinite.{0})

abbreviation pre_Radon := weak_dual ℝ (C(X,ℝ))

variable {X}

noncomputable theory

def indicator {X : Profinite.{0}} {T : discrete_quotient X} (t : T) : C(X,ℝ) :=
{ to_fun := set.indicator (T.proj ⁻¹' {t}) 1,
  continuous_to_fun := sorry }

def pre_Radon.is_bdd (μ : X.pre_Radon) (p c : ℝ≥0) : Prop :=
∀ (T : discrete_quotient X),
  ∑ t : T, (∥ μ (indicator t) ∥₊)^(p : ℝ) ≤ c

variables (X)
def Radon (p c : ℝ≥0) : Top.{0} :=
Top.of { μ : X.pre_Radon | μ.is_bdd p c }
variables {X}

def map_C {X Y : Profinite.{0}} (f : X ⟶ Y) :
  C(Y,ℝ) →L[ℝ] C(X,ℝ) :=
{ to_fun := λ g, g.comp f,
  map_add' := λ g1 g2, rfl,
  map_smul' := λ g1 g2, rfl,
  cont := continuous_map.continuous_comp_left f }

def map_pre_Radon {X Y : Profinite.{0}} (f : X ⟶ Y) :
  X.pre_Radon →L[ℝ] Y.pre_Radon :=
{ to_fun := λ g, g.comp (map_C f),
  map_add' := λ a b, rfl,
  map_smul' := λ a b, rfl,
  cont := begin
    apply weak_dual.continuous_of_continuous_eval, intros ff,
    apply weak_dual.eval_continuous
  end }

lemma pre_Radon.is_bdd_map {X Y : Profinite.{0}} (f : X ⟶ Y)
  (p c : ℝ≥0) (μ : X.pre_Radon) (hμ : μ.is_bdd p c) :
  (map_pre_Radon f μ).is_bdd p c :=
sorry

def map_Radon {X Y : Profinite.{0}} (f : X ⟶ Y) (p c : ℝ≥0) :
  X.Radon p c ⟶ Y.Radon p c :=
{ to_fun := λ μ, ⟨map_pre_Radon f μ.1, pre_Radon.is_bdd_map f p c μ.1 μ.2⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    apply continuous_linear_map.continuous
  end }

def Radon_functor (p c) : Profinite.{0} ⥤ Top.{0} :=
{ obj := λ X, X.Radon p c,
  map := λ X Y f, map_Radon f _ _,
  map_id' := begin
    intros X, ext, dsimp [map_Radon, map_pre_Radon, map_C],
    congr, ext, refl,
  end,
  map_comp' := begin
    intros X Y Z f g, ext, refl,
  end } .

-- Key calculation 1
def real_measures_iso (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  real_measures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c ⋙ CompHaus_to_Top ≅
  Fintype.to_Profinite ⋙ Radon_functor p c := sorry

-- Key calculation 2: Radon_functor should commute with the limit given by `X.as_limit`,
-- which is the construction that exhibits `X` as a limit of its discrete quotients.

end Profinite
