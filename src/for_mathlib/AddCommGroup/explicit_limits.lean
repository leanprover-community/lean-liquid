import algebra.category.Group.limits
import category_theory.limits.concrete_category

universe u

namespace Ab

open category_theory
open category_theory.limits

variables {J : Type u} [category_theory.small_category J] (K : J ⥤ Ab.{u})

lemma comp_apply {A B C : Ab} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
  (f ≫ g) a = g (f a) := rfl

instance : add_comm_group (K ⋙ category_theory.forget _).sections :=
{ add := λ u v, ⟨ u + v, λ i j f, begin
    have u2 := u.2 f,
    have v2 := v.2 f,
    dsimp at *,
    simp [u2,v2],
  end⟩,
  add_assoc := λ a b c, by { ext, simp [add_assoc] },
  zero := ⟨0, λ i j f, by { dsimp, simp }⟩,
  zero_add := λ a, by { ext, dsimp, simp },
  add_zero := λ a, by { ext, dsimp, simp },
  neg := λ t, ⟨ -t, begin
    intros i j f,
    have t2 := t.2 f,
    dsimp at *,
    simp [t2],
  end ⟩,
  add_left_neg := λ a, by { ext, change - (a.1 x) + a.1 x = 0, simp },
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

lemma is_limit_ext {K : J ⥤ Ab.{u}} (C : limit_cone K) (x y : C.cone.X)
  (h : ∀ j : J, C.cone.π.app j x = C.cone.π.app j y) : x = y :=
limits.concrete.is_limit_ext  _ C.2 _ _ h

noncomputable
instance (J : Type u) [small_category J] (K : J ⥤ Ab.{u}) :
  creates_limit K (forget Ab) :=
creates_limit_of_reflects_iso $ λ C hC,
{ lifted_cone := explicit_limit_cone _,
  valid_lift := (types.limit_cone_is_limit _).unique_up_to_iso hC,
  makes_limit := explicit_limit_cone_is_limit _ }

-- Do we have this somewhere else?
noncomputable
instance forget_creates_limits : creates_limits (forget Ab) :=
by { constructor, introsI J hJ, constructor }

end Ab
