import category_theory.abelian.exact

namespace category_theory

universes v u u'

open category_theory.limits

variables {A : Type u} {B : Type u'} [category.{v} A] [category.{v} B]
  [abelian A] [abelian B] (F : A ⥤ B) [functor.additive F]
  [preserves_finite_limits F] [preserves_finite_colimits F]

lemma preserves_exact {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)
  (h : exact f g) : exact (F.map f) (F.map g) :=
begin
  rw abelian.exact_iff,
  split,
  { rw [← F.map_comp, h.w, F.map_zero] },
  { let eK : F.obj (kernel g) ≅ kernel (F.map g) :=
      limits.preserves_kernel.iso _ _,
    let eQ : F.obj (cokernel f) ≅ cokernel (F.map f) :=
      limits.preserves_cokernel.iso _ _,
    have : kernel.ι (F.map g) = eK.inv ≫ F.map (kernel.ι _),
    { rw iso.eq_inv_comp, simp, },
    rw this, clear this,
    have : cokernel.π (F.map f) = F.map (cokernel.π _) ≫ eQ.hom,
    { rw ← iso.comp_inv_eq, simp },
    rw this, clear this,
    simp only [category.assoc, ← F.map_comp_assoc],
    rw abelian.exact_iff at h,
    rw h.2,
    simp }
end

end category_theory
