import order.category.PartialOrder

namespace PartialOrder

open category_theory

variables {J : Type*} [category J] (F : J ⥤ PartialOrder)

structure Grothendieck :=
(base : J)
(fiber : F.obj base)

namespace Grothendieck

variable {F}

@[ext]
structure hom (X Y : Grothendieck F) :=
(base : X.base ⟶ Y.base)
(fiber' : (F.map base) X.fiber ≤ Y.fiber . obviously)

restate_axiom hom.fiber'

end Grothendieck

instance : category (Grothendieck F) :=
{ hom := Grothendieck.hom,
  id := λ X, ⟨𝟙 _⟩,
  comp := λ X Y Z f g, ⟨f.base ≫ g.base, begin
    simp only [auto_param_eq, category_theory.coe_comp, category_theory.functor.map_comp],
    refine le_trans _ g.fiber,
    apply (F.map g.base).monotone,
    exact f.fiber
  end ⟩ }

end PartialOrder
