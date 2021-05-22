import for_mathlib.Profinite.compat_discrete_quotient

noncomputable theory

open category_theory

namespace Profinite

variables (F : arrow Profinite) (surj : function.surjective F.hom)

open discrete_quotient

/-- A diagram of arrows construction from discrete quotients of F.left. -/
@[simps]
def arrow_diagram : discrete_quotient F.left ⥤ arrow Profinite :=
{ obj := λ S, S.make_arrow surj,
  map := λ S T f,
  { left := ⟨of_le $ le_of_hom f⟩,
    right := ⟨of_le $ make_right_mono surj S T $ le_of_hom f⟩ } }.

/-- A cone which is a limit expressing an arrow as a limit. -/
@[simps]
def arrow_cone : limits.cone (arrow_diagram F surj) :=
{ X := F,
  π := { app := λ S, S.make_hom surj } }

end Profinite
