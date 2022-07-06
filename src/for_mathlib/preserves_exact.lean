import category_theory.abelian.exact
import for_mathlib.split_exact

universes v u u'

namespace category_theory

namespace functor

open category_theory.limits

variables {A : Type u} {B : Type u'} [category.{v} A] [category.{v} B]
  [abelian A] [abelian B] (F : A ⥤ B) [functor.additive F]
  [preserves_finite_limits F] [preserves_finite_colimits F]

variables {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma map_exact (h : exact f g) : exact (F.map f) (F.map g) :=
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

lemma map_short_exact (h : short_exact f g) : short_exact (F.map f) (F.map g) :=
begin
  rcases h with ⟨hf, hg, hfg⟩,
  haveI : mono (F.map f),
  { rw (abelian.tfae_mono X f).out 0 2 at hf,
    rw (abelian.tfae_mono (F.obj X) (F.map f)).out 0 2,
    have := F.map_exact _ _ hf, rwa F.map_zero at this, },
  haveI : epi (F.map g),
  { rw (abelian.tfae_epi Z g).out 0 2 at hg,
    rw (abelian.tfae_epi (F.obj Z) (F.map g)).out 0 2,
    have := F.map_exact _ _ hg, rwa F.map_zero at this, },
  refine ⟨F.map_exact f g hfg⟩,
end

end functor

end category_theory
