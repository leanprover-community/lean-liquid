import for_mathlib.derived.derived_cat
import for_mathlib.derived.example
import for_mathlib.short_exact

open category_theory category_theory.triangulated category_theory.limits

namespace homological_complex

variables {A : Type*} [category A] [abelian A]
variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

@[simps]
noncomputable def cone.π (w : ∀ i, f.f i ≫ g.f i = 0) :
  cone f ⟶ Z :=
{ f := λ i, biprod.snd ≫ g.f i,
  comm' := λ i j hij, begin
    dsimp at hij, subst j, dsimp [cone.d], rw [if_pos rfl, biprod.lift_snd_assoc],
    ext,
    { simp only [exact.w_assoc, zero_comp, category.assoc, biprod.inl_desc_assoc,
        category.id_comp, w, exact_inl_snd], },
    { simp only [category.assoc, biprod.inr_snd_assoc, biprod.inr_desc_assoc, g.comm], }
  end }

--generalize
@[simps]
noncomputable def kernel : cochain_complex A ℤ :=
{ X := λ i, kernel (f.f i),
  d := λ i j, kernel.map (f.f i) (f.f j) (X.d i j) (Y.d i j) (f.comm i j),
  shape' := λ i j hij, by { ext, simp only [kernel.lift_ι, zero_comp, X.shape i j hij, comp_zero] },
  d_comp_d' := λ i j k hij hjk, begin
    ext,
    simp only [category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, zero_comp, comp_zero, d_comp_d],
  end }

@[simps]
noncomputable def kernel.ι : kernel f ⟶ X :=
{ f := λ i, kernel.ι _,
  comm' := λ i j hij, by simp only [kernel_d, kernel.lift_ι] }

instance kernel.ι_mono (n : ℕ) : mono ((kernel.ι f).f n) :=
show mono (limits.kernel.ι (f.f n)), by apply_instance

end homological_complex
