import algebra.category.Group.limits
import category_theory.limits.concrete_category

universes u v

namespace Ab

open category_theory
open category_theory.limits

variables {J : Type u} [category_theory.small_category J] (K : J ⥤ Ab.{max u v})

lemma comp_apply {A B C : Ab} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
  (f ≫ g) a = g (f a) := rfl

instance : add_comm_group (K ⋙ category_theory.forget _).sections :=
{ add := λ u v, ⟨ u + v, λ i j f, begin
    have u2 := u.2 f,
    have v2 := v.2 f,
    dsimp only [functor.comp_map, pi.add_apply, forget_map_eq_coe, subtype.val_eq_coe] at ⊢ u2 v2,
    simp only [u2, v2, map_add],
  end⟩,
  add_assoc := λ a b c, by { ext, simp only [add_assoc, subtype.coe_mk] },
  zero := ⟨0, λ i j f, by { dsimp only [functor.comp_map, pi.zero_apply,
    forget_map_eq_coe], rw [map_zero] }⟩,
  zero_add := λ a, by { ext, simp only [subtype.coe_mk, zero_add] },
  add_zero := λ a, by { ext, simp only [subtype.coe_mk, add_zero] },
  neg := λ t, ⟨ -t, begin
    intros i j f,
    have t2 := t.2 f,
    dsimp only [functor.comp_map, pi.neg_apply, forget_map_eq_coe, subtype.val_eq_coe] at ⊢ t2,
    simp only [map_neg, t2],
  end ⟩,
  add_left_neg := λ a, by { ext, change - (a.1 x) + a.1 x = 0, simp only [add_left_neg] },
  add_comm := λ a b, by { ext, change (a.1 x) + (b.1 x) = (b.1 x) + (a.1 x), rw [add_comm] } }

def explicit_limit_cone : cone K :=
{ X := AddCommGroup.of (K ⋙ category_theory.forget _).sections,
  π :=
  { app := λ j,
    { to_fun := λ t, t.1 j,
      map_zero' := rfl,
      map_add' := λ x y, rfl },
    naturality' := begin
      intros i j f,
      ext,
      simpa using (x.2 f).symm,
    end } }

def explicit_limit_cone_is_limit : is_limit (explicit_limit_cone K) :=
{ lift := λ S,
  { to_fun := λ t, ⟨λ j, S.π.app j t, begin
      intros i j f,
      dsimp,
      rw ← S.w f,
      refl,
    end⟩,
    map_zero' := by { ext, dsimp, simpa },
    map_add' := λ x y, by { ext, dsimp, simpa } },
  fac' := begin
    intros S j,
    ext,
    refl,
  end,
  uniq' := begin
    intros S m hm,
    ext,
    simpa [← hm],
  end }

noncomputable
def barx : preserves_limit K (forget Ab.{max u v}) :=
preserves_limits_of_shape.preserves_limit

noncomputable
instance foo {K : J ⥤ Ab.{u}} : preserves_limit K (forget Ab.{u}) :=
barx.{u u} K

lemma is_limit_ext {K : J ⥤ Ab.{u}} (C : limit_cone K) (x y : C.cone.X)
  (h : ∀ j : J, C.cone.π.app j x = C.cone.π.app j y) : x = y :=
limits.concrete.is_limit_ext K C.2 _ _ h

noncomputable
instance forget_creates_limit (J : Type u) [small_category J] (K : J ⥤ Ab.{max u v}) :
  creates_limit K (forget Ab) :=
creates_limit_of_reflects_iso $ λ C hC,
{ lifted_cone := explicit_limit_cone _,
  valid_lift := (types.limit_cone_is_limit _).unique_up_to_iso hC,
  makes_limit := explicit_limit_cone_is_limit _ }

-- Do we have this somewhere else?
noncomputable
instance forget_creates_limits : creates_limits (forget Ab.{max u v}) :=
by { constructor, introsI J hJ, constructor, intros K, apply Ab.forget_creates_limit.{_ u} J K }

-- Do we have this somewhere else?
noncomputable
instance forget_creates_limits' : creates_limits (forget Ab.{u}) :=
Ab.forget_creates_limits.{u u}

end Ab
