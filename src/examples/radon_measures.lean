import challenge
import Radon.png

/-!
In this file we explain how the condensed abelian group `ℳ_{p} S`, for a profinite set `S`,
is related to the space of signed `p`-Radon measures on `S`.
-/

noncomputable theory

open_locale liquid_tensor_experiment nnreal zero_object big_operators
open liquid_tensor_experiment category_theory category_theory.limits
  opposite pseudo_normed_group topological_space

variables (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)]

/-
The functor which associates a condensed abelian group to a
CompHaus-ly filtered pseudo normed group.
-/
example : CompHausFiltPseuNormGrp.{0} ⥤ Condensed.{0} Ab.{1} :=
CompHausFiltPseuNormGrp.to_Condensed

/-
On objects, the functor `CompHausFiltPseuNormGrp.to_Condensed` behaves as expected.
For technical reasons related to size issues in topos theory,
we need to bump to a higher universe using `ulift`.
-/
example (X : CompHausFiltPseuNormGrp.{0}) (S : Profinite.{0}) :
(Γ_ (CompHausFiltPseuNormGrp.to_Condensed.obj X) S : Type 1) =
(ulift.{1}  -- universe bump
  { f : S → X |  -- the set of all functions `S → X` such that...
    ∃ (c : ℝ≥0)  -- there exists a non-negative real `c`,
    (g : S → filtration X c), -- a map `g` from `S` to the `c`-th term of the filtration of `X`
    continuous g ∧  -- such that `g` is continuous and
    f = coe ∘ g }) :=  -- `f` is the composition of `g` with the inclusion.
rfl

/-
The group structure on the `S`-sections of the condensed abelian group associated to
`X : CompHausFiltPseuNormGrp` is the obvious one.
-/
example (X : CompHausFiltPseuNormGrp.{0}) (S : Profinite.{0})
  (f g : Γ_ (CompHausFiltPseuNormGrp.to_Condensed.obj X) S) (s : S) :
  (f + g).down.val s = f.down.val s + g.down.val s := rfl

/-
The category `CompHausFiltPseuNormGrp₁` is similar to that of
CompHaus-ly filtered pseudo-normed groups, except that the filtration is assumed to be exhaustive
and the morphisms are strict.
`CHFPNG₁_to_CHFPNGₑₗ` is the obvious forgetful functor between these two categories.
-/
example : CompHausFiltPseuNormGrp₁ ⥤ CompHausFiltPseuNormGrp :=
CHFPNG₁_to_CHFPNGₑₗ

example (X : CompHausFiltPseuNormGrp₁) :
  (CHFPNG₁_to_CHFPNGₑₗ.obj X : Type*) = X := rfl

/- The condensed abelian group `ℳ_p(S)` is isomorphic to the condensed abelian group associated
to the CompHaus-ly filtered pseudo normed group `S.Radon_png p`.
In the examples below, we explain how `S.Radon_png p` is related to Radon measures.
-/
example (S : Profinite.{0}) :
  (ℳ_{p} S) ≅
  CompHausFiltPseuNormGrp.to_Condensed.obj
  (CHFPNG₁_to_CHFPNGₑₗ.obj $ S.Radon_png p) :=
CompHausFiltPseuNormGrp.to_Condensed.map_iso $
CHFPNG₁_to_CHFPNGₑₗ.map_iso $ (S.Radon_png_iso p).symm

/-
Any element of `S.Radon_png p` induces a continuous linear map from `C(S,ℝ)` to `ℝ`.
-/
example (S : Profinite.{0}) (μ : S.Radon_png p) : C(S,ℝ) →L[ℝ] ℝ :=
μ.1

/-
If `μ : S.Radon_png p`, then there exists a nonnegative real `c` such that for all partitions of
`S` into clopens `S = U_1 ∪ ⋯ ∪ U_n`, letting `I_i` denote the indicator function of `U_i`, one has
`∑ i, ∥ μ (I_i) ∥^p ≤ c`.
-/
example (S : Profinite.{0}) (μ : S.Radon_png p) :
  ∃ c : ℝ≥0,
  ∀ (ι : Fintype.{0}) (e : ι → set S)
    (I : indexed_partition e) (he : ∀ i, is_clopen (e i)),
    ∑ i : ι, ∥ μ.1 (clopens.indicator ⟨e i, he i⟩) ∥₊^(p : ℝ) ≤ c :=
begin
  obtain ⟨c,hc⟩ := μ.2,
  use c,
  rwa weak_dual.bdd_iff_indexed_parition at hc,
end

/-- Conversely, if we are given a continuous linear map `C(S,ℝ) → ℝ` and a nonnegative real `c`
satisfying the inequality appearing in the example above, then we may construct an element of
the `c`-th term of the filtration of `S.Radon_png p`.
-/
example (S : Profinite.{0}) (μ : C(S,ℝ) →L[ℝ] ℝ) (c : ℝ≥0)
  (h : ∀ (ι : Fintype.{0}) (e : ι → set S)
      (I : indexed_partition e) (he : ∀ i, is_clopen (e i)),
      ∑ i : ι, ∥ μ (clopens.indicator ⟨e i, he i⟩) ∥₊^(p : ℝ) ≤ c) :
  filtration (S.Radon_png p) c :=
{ val := ⟨μ,c, by { rw weak_dual.bdd_iff_indexed_parition, assumption }⟩,
  property := by { erw ← weak_dual.bdd_iff_indexed_parition at h, assumption } }

/-- The canonical embedding of `S.Radon_png p` into the weak dual of `C(S,ℝ)`. -/
def embedding_into_the_weak_dual (S : Profinite.{0}) :
  S.Radon_png p → weak_dual ℝ C(S,ℝ) := λ μ, μ.1

/-- The topology of the `c`-th term of the filtration of `S.Radon_png p` is induced
by the weak topology on the set of continuous linear map `C(S,ℝ) → ℝ`. -/
example (S : Profinite.{0}) (c : ℝ≥0) :
  inducing (λ μ : filtration (S.Radon_png p) c, embedding_into_the_weak_dual p S μ) := ⟨rfl⟩

/-- The group structure on `S.Radon_png p` is also induced by the weak dual. -/
example (S : Profinite.{0}) (F G : S.Radon_png p) :
  embedding_into_the_weak_dual p S (F + G) =
  embedding_into_the_weak_dual p S F +
  embedding_into_the_weak_dual p S G := rfl
