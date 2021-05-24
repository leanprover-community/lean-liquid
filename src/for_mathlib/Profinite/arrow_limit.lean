import for_mathlib.Profinite.compat_discrete_quotient
import for_mathlib.Cech.split
import for_mathlib.arrow
import topology.category.Profinite.as_limit

noncomputable theory

open category_theory

namespace Profinite

variables (F : arrow Profinite) (surj : function.surjective F.hom)

open discrete_quotient

/-- A diagram of arrows construction from discrete quotients of F.left. -/
@[simps]
def fintype_arrow_diagram : discrete_quotient F.left ⥤ arrow Fintype :=
{ obj := λ S,
  { left := Fintype.of S,
    right := Fintype.of $ S.make F.hom surj,
    hom := discrete_quotient.map (S.make_le_comap _ _) },
  map := λ S T f,
  { left := of_le $ le_of_hom f,
    right := of_le $ make_right_mono F.hom surj S T $ le_of_hom f } }.

/-- A diagram of arrows construction from discrete quotients of F.left. -/
@[simps]
def arrow_diagram : discrete_quotient F.left ⥤ arrow Profinite :=
fintype_arrow_diagram F surj ⋙ Fintype.to_Profinite.map_arrow
/-
{ obj := λ S,
  { left := Profinite.of S,
    right := Profinite.of $ S.make F.hom surj,
    hom := ⟨discrete_quotient.map (S.make_le_comap _ _),
      discrete_quotient.map_continuous _⟩ },
  map := λ S T f,
  { left := ⟨of_le $ le_of_hom f⟩,
    right := ⟨of_le $ make_right_mono F.hom surj S T $ le_of_hom f⟩ } }.
-/

/-- The left diagram associated to arrow_diagram. -/
abbreviation left_arrow_diagram : discrete_quotient F.left ⥤ Profinite :=
arrow_diagram F surj ⋙ arrow.left_func

/-- The right diagram associated to arrow_diagram. -/
abbreviation right_arrow_diagram : discrete_quotient F.left ⥤ Profinite :=
arrow_diagram F surj ⋙ arrow.right_func

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

/-- the limit cone assocciated to arrow_diagram -/
@[simps]
def arrow_limit_cone : limits.limit_cone (arrow_diagram F surj) :=
arrow.limit_cone _ ⟨_,limit_cone_is_limit _⟩ ⟨_,limit_cone_is_limit _⟩

/-- lifing arrow_cone gives an isomorphism on the left -/
instance arrow_is_iso_lift_left : is_iso ((arrow_limit_cone F surj).is_limit.lift
  (arrow_cone F surj)).left := Profinite.is_iso_as_limit_cone_lift _

/-- lifing arrow_cone gives an isomorphism on the right -/
instance arrow_is_iso_lift_right : is_iso ((arrow_limit_cone F surj).is_limit.lift
  (arrow_cone F surj)).right := is_iso_of_bijective _
begin
  split,
  { intros x y h,
    apply discrete_quotient.eq_of_proj_eq,
    intros S,
    apply_fun subtype.val at h,
    let T : discrete_quotient F.left := S.comap F.hom.continuous,
    let R : discrete_quotient F.right := T.make F.hom surj,
    have hR : R ≤ S,
    { apply discrete_quotient.make_right_le,
      tauto },
    apply_fun (λ e, e T) at h,
    have := discrete_quotient.of_le_proj_apply hR,
    rw [← this, ← this],
    congr' 1 },
  { intros x,
    cases x with x hx,
    dsimp at x hx,
    let Us : Π (I : discrete_quotient F.right), I := λ I,
      of_le (make_right_le _ _ _ _ (by tauto)) (x $ I.comap F.hom.continuous),
    rcases discrete_quotient.exists_of_compat Us _ with ⟨y,hy⟩,
    { refine ⟨y,_⟩,
      ext I : 2,
      dsimp at *,
      let J : discrete_quotient F.right := (I.make F.hom surj),
      let II : discrete_quotient F.left := J.comap F.hom.continuous ⊓ I,
      have h1 : II ≤ I := inf_le_right,
      have h2 : II ≤ J.comap F.hom.continuous := inf_le_left,
      rw ← hx (hom_of_le h1),
      rw hy,
      dsimp [Us],
      rw ← hx (hom_of_le h2),
      rw ← of_le_comp_apply },
    { intros A B h,
      dsimp [Us],
      have := comap_mono F.hom.continuous h,
      rw ← hx (hom_of_le this),
      rw [← of_le_comp_apply, ← of_le_comp_apply] } },
end

/-- The isomorphism of cones showing that arrow_cone is a limit cone. -/
def arrow_cone_iso : arrow_cone F surj ≅ (arrow_limit_cone F surj).cone :=
limits.cones.ext (as_iso $ (arrow_limit_cone F surj).is_limit.lift (arrow_cone F surj))
  (λ _, rfl)

/-- arrow_cone is a limit cone. -/
def is_limit_arrow_cone : limits.is_limit (arrow_cone F surj) :=
limits.is_limit.of_iso_limit (arrow_limit_cone F surj).is_limit
  (arrow_cone_iso F surj).symm

end Profinite
