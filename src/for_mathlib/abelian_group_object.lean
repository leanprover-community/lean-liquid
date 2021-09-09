import category_theory.limits.shapes.binary_products
import category_theory.monoidal.CommMon_
import category_theory.monoidal.of_chosen_finite_products
import category_theory.limits.types
import algebra.category.Group

namespace category_theory
open category_theory.limits category_theory.monoidal_category

variables (C : Type*) [category C]

noncomputable theory

class cartesian :=
[hbp : has_binary_products C]
[ht : has_terminal C]

variables [cartesian C]
namespace cartesian

instance : has_binary_products C := cartesian.hbp
instance : has_terminal C := cartesian.ht

instance [cartesian C] : monoidal_category C := monoidal_of_chosen_finite_products
  ⟨limit.cone _, limit.is_limit _⟩ (λ X Y, ⟨limit.cone _, limit.is_limit _⟩)

@[simp] lemma tensor_hom_eq {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
  f ⊗ g = limits.prod.map f g :=
begin
  change limits.prod.lift _ _ = _,
  tidy,
end

@[simp] lemma α_eq (X Y Z : C) : α_ X Y Z = limits.prod.associator _ _ _ := rfl

instance : braided_category C := { braiding := λ X Y, limits.prod.braiding X Y }

end cartesian

structure Group_ extends Mon_ C :=
(inv : X ⟶ X)
(inv_mul : prod.lift inv (𝟙 X) ≫ mul = terminal.from X ≫ one)
(mul_inv : prod.lift (𝟙 X) inv ≫ mul = terminal.from X ≫ one)

structure Ab_ extends CommMon_ C :=
(inv : X ⟶ X)
(inv_mul : prod.lift inv (𝟙 X) ≫ mul = terminal.from X ≫ one)
(mul_inv : prod.lift (𝟙 X) inv ≫ mul = terminal.from X ≫ one)

section examples

instance : cartesian Type* := {}

def types.prod_cone (A B : Type*) : cone (pair A B) :=
  binary_fan.mk (_root_.prod.fst : A × B → A) _root_.prod.snd

def types.prod_cone_is_limit (A B : Type*) : is_limit (types.prod_cone A B) :=
{ lift := λ (S : binary_fan A B) x, ⟨S.fst x, S.snd x⟩,
  fac' := begin
    rintro S (j|j),
    tidy,
  end,
  uniq' := begin
    rintro S m h,
    ext,
    { specialize h walking_pair.left, tidy },
    { specialize h walking_pair.right, tidy },
  end }

def types.terminal_cone : cone (functor.empty Type*) :=
{ X := punit,
  π :=
  { app := λ X t, X.elim } }

def types.terminal_cone_is_limit : is_limit types.terminal_cone :=
{ lift := λ S t, punit.star }

def Ab__to_Ab (M : Ab_ Type*) : Ab :=
{ α := M.X,
  str :=
  { add := λ x y, let F := limit.lift _ (types.prod_cone M.X M.X) in (F ≫ M.mul) ⟨x,y⟩,
    add_assoc := sorry,
    zero := ((limit.lift _ types.terminal_cone) ≫ M.one) punit.star,
    zero_add := sorry,
    add_zero := sorry,
    neg := λ x, M.inv x,
    add_left_neg := sorry,
    add_comm := sorry } }

end examples

end category_theory
