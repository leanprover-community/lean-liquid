import topology.category.Profinite
import category_theory.arrow

open category_theory

noncomputable theory

namespace Profinite

variable (f : arrow Profinite)

@[simps]
def fibprod (n : ℕ) : arrow Profinite ⥤ Profinite :=
{ obj := λ f, limits.wide_pullback f.right (λ i : ulift (fin n), f.left) (λ i, f.hom),
  map := λ f g ff, limits.wide_pullback.lift (limits.wide_pullback.base _ ≫ ff.right)
    (λ i, limits.wide_pullback.π _ i ≫ ff.left)
    begin
      intro i,
      erw [category.assoc, ff.w, ← category.assoc],
      rw limits.wide_pullback.π_arrow _ _,
      refl,
    end,
  map_id' := begin
    intro f,
    apply limits.wide_pullback.hom_ext,
    { simp },
    { simp },
  end,
  map_comp' := begin
    intros f g h ff gg,
    apply limits.wide_pullback.hom_ext,
    { simp },
    { simp },
  end }

end Profinite
