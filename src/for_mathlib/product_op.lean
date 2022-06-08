import category_theory.limits.shapes.products

namespace category_theory.limits

open category_theory

universes v u
variables {C : Type u} [category.{v} C]

open opposite

noncomputable
def op_product_iso {α : Type v} (X : α → C) [has_product X] [has_coproduct (λ a, op (X a))] :
  op (∏ X) ≅ ∐ (λ a, op (X a)) :=
{ hom := quiver.hom.op (pi.lift $ λ a, quiver.hom.unop (sigma.ι (λ a, op (X a)) a) ≫
    eq_to_hom (unop_op _)) ≫ eq_to_hom (op_unop _),
  inv := sigma.desc $ λ a, quiver.hom.op $ pi.π _ _,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

end category_theory.limits
