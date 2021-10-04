import generalisation_linter
import category_theory.limits.concrete_category
import topology.category.Profinite.as_limit
import for_mathlib.Profinite.compat_discrete_quotient
import for_mathlib.Cech.split

noncomputable theory

open category_theory

universe u

namespace Profinite

variables (F : arrow Profinite.{u}) (surj : function.surjective F.hom)

open discrete_quotient

/-- A diagram of arrows construction from discrete quotients of F.left. -/
@[simps]
def fintype_arrow_diagram : discrete_quotient F.left ⥤ arrow Fintype.{u} :=
{ obj := λ S,
  { left := Fintype.of S,
    right := Fintype.of $ S.make F.hom surj,
    hom := discrete_quotient.map (S.make_le_comap _ _) },
  map := λ S T f,
  { left := of_le $ le_of_hom f,
    right := of_le $ make_right_mono F.hom surj S T $ le_of_hom f } }.

/-- A diagram of arrows construction from discrete quotients of F.left. -/
@[simps]
def arrow_diagram : discrete_quotient F.left ⥤ arrow Profinite.{u} :=
fintype_arrow_diagram F surj ⋙ Fintype.to_Profinite.map_arrow

/-- The left diagram associated to arrow_diagram. -/
abbreviation left_arrow_diagram : discrete_quotient F.left ⥤ Profinite.{u} :=
arrow_diagram F surj ⋙ arrow.left_func

/-- The right diagram associated to arrow_diagram. -/
abbreviation right_arrow_diagram : discrete_quotient F.left ⥤ Profinite.{u} :=
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
    erw classical.some_spec (arrow_diagram_surjective F surj S x),
    refl,
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

/-- A helper definition used for `arrow_limit_cone`. -/
def arrow_diagram_snd_preserves :
  limits.preserves_limit (arrow_diagram F surj ⋙ comma.snd _ _) (𝟭 _) :=
begin
  have h := limits.id_preserves_limits.preserves_limits_of_shape,
  have hh := h.preserves_limit,
  exact hh,
end

/-- the limit cone assocciated to arrow_diagram -/
@[simps]
def arrow_limit_cone : limits.limit_cone (arrow_diagram F surj) :=
{ cone := @comma.cone_of_preserves _ _ _ _ _ _ _ _ _ _ _
  (arrow_diagram_snd_preserves _ _) (limit_cone _) _ (limit_cone_is_limit _),
  is_limit := @comma.cone_of_preserves_is_limit _ _ _ _ _ _ _ _ _ _ _
    (arrow_diagram_snd_preserves _ _) _ (limit_cone_is_limit _) _ _ }

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
      dsimp [comma.cone_of_preserves_is_limit,
        limit_cone_is_limit, CompHaus.limit_cone_is_limit,
        Top.limit_cone_is_limit],
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

@[simps]
def left_arrow_cone : limits.cone (left_arrow_diagram F surj) :=
functor.map_cone _ (arrow_cone F surj)

@[simps]
def right_arrow_cone : limits.cone (right_arrow_diagram F surj) :=
functor.map_cone _ (arrow_cone F surj)

instance left_arrow_cone_lift_is_iso : is_iso $
  (limit_cone_is_limit $ left_arrow_diagram F surj).lift (left_arrow_cone F surj) :=
Profinite.arrow_is_iso_lift_left _ _

instance right_arrow_cone_lift_is_iso : is_iso $
  (limit_cone_is_limit $ right_arrow_diagram F surj).lift (right_arrow_cone F surj) :=
Profinite.arrow_is_iso_lift_right _ _

@[simps]
def left_arrow_cone_iso : left_arrow_cone F surj ≅
  (limit_cone $ left_arrow_diagram F surj) :=
limits.cones.ext (as_iso $ (limit_cone_is_limit $ left_arrow_diagram F surj).lift _)
  (λ _ , rfl)

@[simps]
def right_arrow_cone_iso : right_arrow_cone F surj ≅
  (limit_cone $ right_arrow_diagram F surj) :=
limits.cones.ext (as_iso $ (limit_cone_is_limit $ right_arrow_diagram F surj).lift _)
  (λ _ , rfl)

/-- The isomorphism of cones showing that arrow_cone is a limit cone. -/
@[simps]
def arrow_cone_iso : arrow_cone F surj ≅ (arrow_limit_cone F surj).cone :=
limits.cones.ext (as_iso $ (arrow_limit_cone F surj).is_limit.lift (arrow_cone F surj))
  (λ _, rfl)

/-- arrow_cone is a limit cone. -/
@[simps]
def is_limit_arrow_cone : limits.is_limit (arrow_cone F surj) :=
limits.is_limit.of_iso_limit (arrow_limit_cone F surj).is_limit
  (arrow_cone_iso F surj).symm

@[simps]
def is_limit_left_arrow_cone : limits.is_limit (left_arrow_cone F surj) :=
limits.is_limit.of_iso_limit (limit_cone_is_limit $ left_arrow_diagram F surj)
  (left_arrow_cone_iso _ _).symm

@[simps]
def is_limit_right_arrow_cone : limits.is_limit (right_arrow_cone F surj) :=
limits.is_limit.of_iso_limit (limit_cone_is_limit $ right_arrow_diagram F surj)
  (right_arrow_cone_iso _ _).symm

open opposite

open_locale simplicial

@[simps]
def Cech_cone_diagram (n : ℕ) : discrete_quotient F.left ⥤ Profinite.{u} :=
arrow_diagram F surj ⋙ simplicial_object.cech_nerve ⋙
  (evaluation _ _).obj (op [n])

def Cech_cone_diagram_proj (n : ℕ) (S : discrete_quotient F.left) (i : fin (n+1)) :
  (Cech_cone_diagram F surj n).obj S ⟶ Profinite.of S :=
limits.wide_pullback.π _ ⟨i⟩

def Cech_cone_diagram_inclusion (n : ℕ) (S : discrete_quotient F.left) :
  (Cech_cone_diagram F surj n).obj S → fin (n+1) → S :=
λ a i, Cech_cone_diagram_proj F surj n S i a

lemma Cech_cone_diagram_inclusion_injective (n : ℕ) (S : discrete_quotient F.left) :
  function.injective (Cech_cone_diagram_inclusion F surj n S) :=
begin
  intros a b h,
  apply category_theory.limits.concrete.wide_pullback_ext',
  rintros ⟨j⟩,
  apply_fun (λ e, e j) at h,
  exact h,
end

instance Cech_cone_diagram_fintype (n : ℕ) (S : discrete_quotient F.left) :
  fintype ((Cech_cone_diagram F surj n).obj S) :=
fintype.of_injective (Cech_cone_diagram_inclusion F surj n S)
  (Cech_cone_diagram_inclusion_injective F surj n S)

@[simps]
def Cech_cone (n : ℕ) : limits.cone (Cech_cone_diagram F surj n) :=
functor.map_cone _ (arrow_cone F surj)

@[simps]
def swap_cone_right (n : ℕ) (S : limits.cone (Cech_cone_diagram F surj n)) :
  limits.cone (right_arrow_diagram F surj) :=
{ X := S.X,
  π := { app := λ T, S.π.app T ≫ limits.wide_pullback.base _,
  naturality' := begin
    intros X Y f,
    dsimp,
    simp [← S.w f],
  end } }

@[simps]
def swap_cone_left (n : ℕ) (i : ulift.{u} (fin (n+1)))
  (S : limits.cone (Cech_cone_diagram F surj n)) :
  limits.cone (left_arrow_diagram F surj) :=
{ X := S.X,
  π :=
  { app := λ T, S.π.app T ≫ limits.wide_pullback.π _ i,
    naturality' := begin
      intros X Y f,
      dsimp,
      simp [← S.w f],
    end } }

@[simps]
def Cech_cone_is_limit (n : ℕ) : limits.is_limit (Cech_cone F surj n) :=
{ lift := λ S, limits.wide_pullback.lift
    ((is_limit_right_arrow_cone F surj).lift $ swap_cone_right _ _ _ _)
    (λ i, (is_limit_left_arrow_cone F surj).lift $ swap_cone_left _ _ _ i _)
    begin
      intros i,
      apply (is_limit_right_arrow_cone F surj).hom_ext,
      intros T,
      simp,
      have : (arrow_cone F surj).X.hom ≫ (right_arrow_cone F surj).π.app T =
        (left_arrow_cone F surj).π.app T ≫
        (whisker_left (arrow_diagram F surj) arrow.left_to_right).app T, by refl,
      erw [this, ← category.assoc,
        (is_limit_left_arrow_cone F surj).fac (swap_cone_left F surj n i S) T],
      simp,
    end,
  fac' := begin
    intros S T,
    apply limits.wide_pullback.hom_ext,
    { intro i,
      dsimp,
      simp,
      have := (is_limit_left_arrow_cone F surj).fac,
      erw this,
      refl },
    { dsimp,
      simp,
      erw (is_limit_right_arrow_cone F surj).fac,
      refl }
  end,
  uniq' := begin
    intros S f h,
    apply limits.wide_pullback.hom_ext,
    { dsimp, simp,
      intros i,
      apply (is_limit_left_arrow_cone F surj).hom_ext,
      intros T,
      simp,
      erw [← h T, category.assoc, limits.wide_pullback.lift_π],
      refl },
    { dsimp, simp,
      apply (is_limit_right_arrow_cone F surj).hom_ext,
      intros T,
      simp,
      erw [← h T, category.assoc, limits.wide_pullback.lift_base],
      refl }
  end }.

end Profinite
#lint only generalisation_linter
