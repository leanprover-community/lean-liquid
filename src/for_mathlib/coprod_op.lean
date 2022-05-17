import category_theory.limits.shapes.products

namespace category_theory.limits

open category_theory

universes v u
variables {A : Type u} [category.{v} A] [has_coproducts A]

open opposite

noncomputable
def op_fan {α : Type v} (X : α → A) : fan (λ a, op (X a)) :=
fan.mk (op $ ∐ X) (λ b, (sigma.ι _ _).op)

noncomputable
def is_limit_op_fan {α : Type v} (X : α → A) :
  is_limit (op_fan X) :=
{ lift := λ S, let e : ∐ X ⟶ S.X.unop := sigma.desc $ λ b, (S.π.app b).unop in
    e.op,
  fac' := begin
    intros S j,
    dsimp [op_fan],
    rw [← op_comp, colimit.ι_desc],
    refl,
  end,
  uniq' := begin
    intros S m hm,
    dsimp,
    rw ← m.op_unop, congr' 1,
    apply colimit.hom_ext,
    intros j,
    simp only [colimit.ι_desc, cofan.mk_ι_app, ← hm],
    refl,
  end }


end category_theory.limits
