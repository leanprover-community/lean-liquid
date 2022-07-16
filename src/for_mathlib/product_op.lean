import category_theory.limits.shapes.products

namespace category_theory.limits

open category_theory category_theory.limits

universes v u
variables {C : Type u} [category.{v} C]

open opposite

noncomputable
def op_product_iso {α : Type v} (X : α → C) [has_product X] [has_coproduct (λ a, op (X a))] :
  op (∏ X) ≅ ∐ (λ a, op (X a)) :=
{ hom := quiver.hom.op (pi.lift $ λ a, quiver.hom.unop (sigma.ι (λ a, op (X a)) a) ≫
    eq_to_hom (unop_op _)) ≫ eq_to_hom (op_unop _),
  inv := sigma.desc $ λ a, quiver.hom.op $ pi.π _ _,
  hom_inv_id' := begin
    apply quiver.hom.unop_inj,
    ext j,
    simp only [eq_to_hom_refl, category.comp_id, unop_comp, quiver.hom.unop_op, category.assoc,
      limit.lift_π, fan.mk_π_app, unop_id_op, category.id_comp],
    rw [← unop_comp, colimit.ι_desc, cofan.mk_ι_app],
    erw [category.id_comp],
    rcases j,
    refl
  end,
  inv_hom_id' := begin
    ext j,
    simp only [eq_to_hom_refl, category.comp_id, colimit.ι_desc_assoc, cofan.mk_ι_app],
    rw [← op_comp, limit.lift_π, fan.mk_π_app],
    rcases j,
    refl
  end }

end category_theory.limits
