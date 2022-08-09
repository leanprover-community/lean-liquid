import examples.Radon.setup

open_locale nnreal big_operators classical

noncomputable theory

open category_theory
open category_theory.limits
open topological_space

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space

namespace Profinite

@[derive topological_space]
def Radon (X : Profinite.{0}) (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  Top.{0} :=
Top.of { μ : weak_dual ℝ C(X,ℝ) // μ.bdd p c }

@[derive topological_space]
def Radon_LC (X : Profinite.{0}) (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  Top.{0} :=
Top.of { μ : weak_dual ℝ (locally_constant X ℝ) // μ.bdd_LC p c }

def map_Radon {X Y : Profinite.{0}} (f : X ⟶ Y)
  (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon p c ⟶ Y.Radon p c :=
{ to_fun := λ μ, ⟨weak_dual.comap f.comap μ.1,
    weak_dual.bdd_comap _ μ.2 _⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    exact continuous_linear_map.continuous _,
  end }

def map_Radon_LC {X Y : Profinite.{0}} (f : X ⟶ Y)
  (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  X.Radon_LC p c ⟶ Y.Radon_LC p c :=
{ to_fun := λ μ, ⟨weak_dual.comap f.comap_LC μ.1,
    weak_dual.bdd_LC_comap _ μ.2 _⟩,
  continuous_to_fun := begin
    apply continuous_subtype_mk,
    refine continuous.comp _ continuous_subtype_coe,
    exact continuous_linear_map.continuous _,
  end }

def Radon_functor (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  Profinite.{0} ⥤ Top.{0} :=
{ obj := λ X, X.Radon p c,
  map := λ X Y f, map_Radon f _ _,
  map_id' := λ X, by { ext, dsimp [map_Radon, weak_dual.comap], congr' 1,
    ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

def Radon_LC_functor (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  Profinite.{0} ⥤ Top.{0} :=
{ obj := λ X, X.Radon_LC p c,
  map := λ X Y f, map_Radon_LC f _ _,
  map_id' := λ X,
    by { ext, dsimp [map_Radon_LC, weak_dual.comap], congr' 1, ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

.

def weak_dual_C_to_LC (X : Profinite.{0}) :
  weak_dual ℝ C(X,ℝ) →L[ℝ] weak_dual ℝ (locally_constant X ℝ) :=
weak_dual.comap $ lc_to_c _

def weak_dual_LC_to_C (X : Profinite.{0}) :
  weak_dual ℝ (locally_constant X ℝ) →ₗ[ℝ] weak_dual ℝ C(X,ℝ) :=
{ to_fun := λ f,
  { to_fun := (locally_constant.pkg X ℝ).extend f,
    map_add' := sorry,
    map_smul' := sorry,
    cont := (locally_constant.pkg X ℝ).continuous_extend },
  map_add' := sorry,
  map_smul' := sorry }

end Profinite
