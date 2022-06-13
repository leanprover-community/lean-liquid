import algebra.category.Group.biproducts

open category_theory
open category_theory.limits

namespace AddCommGroup

universes v u

def pi_π {α : Type v} (X : α → AddCommGroup.{max v u}) (i) :
  AddCommGroup.of (Π i, X i) ⟶ X i :=
pi.eval_add_monoid_hom _ _

def pi_fan {α : Type v} (X : α → AddCommGroup.{max v u}) : fan X :=
fan.mk (AddCommGroup.of $ Π i, X i)
(λ b, pi_π _ _)

def pi_lift {α : Type v} {Y : AddCommGroup.{max v u}} (X : α → AddCommGroup.{max v u})
  (f : Π a, Y ⟶ X a) : Y ⟶ AddCommGroup.of (Π i, X i) :=
{ to_fun := λ y i, f _ y,
  map_zero' := by { ext, simp },
  map_add' := λ x y, by { ext, simp } }

@[simp, reassoc]
lemma pi_lift_π {α : Type v} {Y : AddCommGroup.{max v u}} (X : α → AddCommGroup.{max v u})
  (f : Π a, Y ⟶ X a) (i) :
  pi_lift X f ≫ pi_π _ i = f _ := by { ext, refl }

lemma pi_hom_ext {α : Type v} {Y : AddCommGroup.{max v u}} (X : α → AddCommGroup.{max v u})
  (f g : Y ⟶ AddCommGroup.of (Π i, X i))
  (h : ∀ i, f ≫ pi_π _ i = g ≫ pi_π _ i) : f = g :=
by { ext y a, specialize h a, apply_fun (λ e, e y) at h, exact h }

def is_limit_pi_fan {α : Type v} (X : α → AddCommGroup.{max v u}) :
  is_limit (pi_fan X) :=
{ lift := λ S, pi_lift _ $ S.π.app,
  fac' := begin
    intros S j,
    apply pi_lift_π,
  end,
  uniq' := begin
    intros S m hm,
    apply pi_hom_ext,
    intros i,
    erw [hm, pi_lift_π],
  end }

end AddCommGroup
