import category_theory.preadditive.yoneda
import for_mathlib.AddCommGroup.kernels

noncomputable theory

universes v

namespace category_theory

namespace limits

section kernel_comparison
variables {C D : Type*} [category.{v} C] [category.{v} D] [has_zero_morphisms C]
  [has_zero_morphisms D] (F : C ⥤ D) [functor.preserves_zero_morphisms F]

lemma kernel_comparison_is_iso_of_is_limit {A₁ A₂ : C} (f : A₁ ⟶ A₂) [has_kernel f]
  [has_kernel (F.map f)] (s : kernel_fork f) (hs₁ : is_limit s)
    (hs₂ : is_limit (kernel_fork.of_ι (F.map s.ι) (show _ ≫ F.map f = 0, by { rw [← F.map_comp, kernel_fork.condition, F.map_zero],}))) :
  is_iso (limits.kernel_comparison f F) :=
begin
  let α : kernel f ≅ s.X := is_limit.cone_point_unique_up_to_iso (limit.is_limit _) hs₁,
  let β : F.obj s.X ≅ kernel (F.map f) := is_limit.cone_point_unique_up_to_iso hs₂
    (limit.is_limit _),
  suffices : limits.kernel_comparison f F = (F.map_iso α ≪≫ β).hom,
  { rw this, apply_instance, },
  rw ← cancel_mono (kernel.ι (F.map f)),
  dsimp only [α, β],
  simp only [kernel_comparison_comp_ι, iso.trans_hom, fork.of_ι_π_app,
    functor.map_iso_hom, category.assoc, limit.cone_point_unique_up_to_iso_hom_comp,
    ← F.map_comp],
  congr',
  rw ← cancel_epi ((limit.is_limit (parallel_pair f 0)).cone_point_unique_up_to_iso hs₁).inv,
  simp only [iso.inv_hom_id_assoc, limit.cone_point_unique_up_to_iso_inv_comp, fork.app_zero_eq_ι],
end

end kernel_comparison

variables {C : Type*} [category C] [preadditive C]

lemma _root_.AddCommGroup.kernel_fork_is_limit {X Y : AddCommGroup} (φ : X ⟶ Y)
  (s : kernel_fork φ) (hs₁ : function.injective s.ι)
    (hs₂ : ∀ (x : X), φ x = 0 → ∃ (z : s.X), s.ι z = x) :
  is_limit s :=
begin
  sorry,
end

instance preadditive_yoneda_kernel_comparison_is_iso (B : C) {A₁ A₂ : Cᵒᵖ} (f : A₁ ⟶ A₂)
  [has_kernel f] : is_iso (limits.kernel_comparison f (preadditive_yoneda.obj B)) :=
begin
  let hs₁ : is_limit ( _ : kernel_fork f) := limit.is_limit _,
  apply kernel_comparison_is_iso_of_is_limit (preadditive_yoneda.obj B) f _ hs₁,
  apply AddCommGroup.kernel_fork_is_limit,
  { intros g₁ g₂ h,
    dsimp at g₁ g₂ h ⊢,
    rw cancel_epi (kernel.ι f).unop at h,
    exact h, },
  { intros x hx,
    dsimp at x hx ⊢,
    use (kernel.lift f x.op (quiver.hom.unop_inj hx)).unop,
    rw ← unop_comp,
    simp only [kernel.lift_ι, quiver.hom.unop_op], },
end

end limits

end category_theory
