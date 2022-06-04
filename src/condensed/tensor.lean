import condensed.adjunctions

noncomputable theory

universes u

open category_theory

namespace condensed

/-- This is the functor that sends `A : Ab` to `M ⊗ A`,
where `M` is a fixed condensed abelian group. -/
def tensor (M : Condensed.{u} Ab.{u+1}) : Ab.{u+1} ⥤ Condensed.{u} Ab.{u+1} :=
sorry

end condensed
