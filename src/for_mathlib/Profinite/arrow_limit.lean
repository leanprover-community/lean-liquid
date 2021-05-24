import for_mathlib.Profinite.compat_discrete_quotient
import for_mathlib.Cech.split

noncomputable theory

open category_theory

namespace Profinite

variables (F : arrow Profinite) (surj : function.surjective F.hom)

open discrete_quotient

/-- A diagram of arrows construction from discrete quotients of F.left. -/
@[simps]
def arrow_diagram : discrete_quotient F.left ⥤ arrow Profinite :=
{ obj := λ S,
  { left := Profinite.of S,
    right := Profinite.of $ S.make F.hom surj,
    hom := ⟨discrete_quotient.map (S.make_le_comap _ _),
      discrete_quotient.map_continuous _⟩ },
  map := λ S T f,
  { left := ⟨of_le $ le_of_hom f⟩,
    right := ⟨of_le $ make_right_mono F.hom surj S T $ le_of_hom f⟩ } }

lemma arrow_diagram_surjective (S : discrete_quotient F.left) :
  function.surjective ((arrow_diagram F surj).obj S).hom :=
begin
  rintro ⟨x⟩,
  obtain ⟨x,rfl⟩ := surj x,
  exact ⟨S.proj x,rfl⟩,
end

instance (S : discrete_quotient F.left) : arrow.split ((arrow_diagram F surj).obj S) :=
{ σ := ⟨λ x, classical.some (arrow_diagram_surjective F surj S x),
    continuous_of_discrete_topology⟩,
  is_splitting' := begin
    ext x,
    have := classical.some_spec (arrow_diagram_surjective F surj S x),
    erw this,
    simp,
  end }

/-- A cone which is a limit expressing an arrow as a limit. -/
@[simps]
def arrow_cone : limits.cone (arrow_diagram F surj) :=
{ X := F,
  π :=
  { app := λ S,
    { left := ⟨S.proj, S.proj_continuous⟩,
      right := ⟨(S.make _ surj).proj,
        (S.make _ surj).proj_continuous⟩ } } }

end Profinite
