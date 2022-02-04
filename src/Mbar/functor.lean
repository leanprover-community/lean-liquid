import for_mathlib.Profinite.extend

import Mbar.pseudo_normed_group
import pseudo_normed_group.category

noncomputable theory

open_locale nnreal

variables (r' : ℝ≥0) [fact (0 < r')]
variables {S₁ S₂ : Type*} [fintype S₁] [fintype S₂]

namespace Mbar

open pseudo_normed_group (filtration level)
open category_theory category_theory.limits

lemma map_zero (f : S₁ → S₂) : map f (0 : Mbar r' S₁) = 0 :=
by { ext, simp only [coe_zero, map_to_fun, pi.zero_apply, finset.sum_const_zero], }

lemma map_add (f : S₁ → S₂) (x y : Mbar r' S₁) : map f (x + y) = map f x + map f y :=
by { ext s n, simp only [map_to_fun, pi.add_apply, coe_add, finset.sum_add_distrib], }

lemma map_strict (f : S₁ → S₂) ⦃c : ℝ≥0⦄ ⦃x : (Mbar r' S₁)⦄
  (hx : x ∈ filtration (Mbar r' S₁) c) : map f x ∈ filtration (Mbar r' S₂) c :=
Mbar.nnnorm_map_le_of_nnnorm_le f _ hx

lemma map_continuous (f : S₁ → S₂) (c : ℝ≥0) :
  continuous (level (map f) (map_strict r' f) c) :=
begin
  let φ := (level (map f) (map_strict r' f) c),
  rw Mbar_le.continuous_iff,
  intros M,
  have : Mbar_le.truncate M ∘ φ = Mbar_bdd.map f ∘ Mbar_le.truncate M, { ext, refl },
  rw this,
  exact continuous_of_discrete_topology.comp Mbar_le.continuous_truncate,
end

lemma map_Tinv (f : S₁ → S₂) (x : Mbar r' S₁) :
  map f (Tinv x) = Tinv (map f x) :=
by ext s ⟨_|n⟩; simp only [map_to_fun, Tinv_zero, Tinv_succ, finset.sum_const_zero]

/-- `Mbar r' S` is functorial in the finite type `S`. -/
@[simps] def fintype_functor : Fintype ⥤ ProFiltPseuNormGrpWithTinv₁ r' :=
{ obj := λ S,
  { M := Mbar r' S,
    exhaustive' := λ x, ⟨∥x∥₊, by rw Mbar.mem_filtration_iff⟩ },
  map := λ S₁ S₂ f,
  { to_fun := map f,
    map_zero' := map_zero r' f,
    map_add' := map_add r' f,
    strict' := map_strict r' f,
    continuous' := map_continuous r' f,
    map_Tinv' := map_Tinv r' f },
  map_id' := by { intros, ext1 x, exact map_id x },
  map_comp' := by { intros X Y Z f g, ext1 x, exact map_comp f x g } }

example (X : Profinite) : has_limit (X.fintype_diagram ⋙ fintype_functor r') :=
by apply_instance

/-- `Mbar r' S` extends to a functor in `S`, for profinite `S`. -/
def functor : Profinite ⥤ ProFiltPseuNormGrpWithTinv₁ r' :=
Profinite.extend (fintype_functor r')

end Mbar
