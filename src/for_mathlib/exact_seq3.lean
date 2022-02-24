import for_mathlib.exact_seq2
import for_mathlib.abelian_category

namespace category_theory
open category_theory.limits

variables {A : Type*} [category A] [abelian A]

noncomputable theory

def exact_seq.w {X₁ X₂ X₃ : A} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
  (e : exact_seq A [f, g]) : f ≫ g = 0 :=
by { rw ← exact_iff_exact_seq at e, exact e.w }

def exact_seq.π {X₁ X₂ X₃ : A} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
  (e : exact_seq A [f, g]) : cokernel f ⟶ X₃ :=
cokernel.desc _ g e.w

def exact_seq.ι {X₁ X₂ X₃ : A} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
  (e : exact_seq A [f, g]) : X₁ ⟶ kernel g :=
kernel.lift _ f e.w

local attribute [instance] abelian.pseudoelement.hom_to_fun

lemma exact_seq.replace
  {X₁ X₂ X₃ X₄ X₅ : A}
  {f₁ : X₁ ⟶ X₂}
  {f₂ : X₂ ⟶ X₃}
  {f₃ : X₃ ⟶ X₄}
  {f₄ : X₄ ⟶ X₅}
  (e : exact_seq A [f₁, f₂, f₃, f₄]) :
  exact (e.extract 0 2).π (e.extract 2 3).ι :=
begin
  apply abelian.pseudoelement.exact_of_pseudo_exact,
  split,
  { intros a,
    simp only [← abelian.pseudoelement.comp_apply],
    suffices : (e.extract 0 2).π ≫ (e.extract 2 3).ι = 0,
    by { rw this, simp },
    ext,
    dsimp [exact_seq.π, exact_seq.ι],
    simpa using (e.extract 1 2).w },
  { intros t ht,
    dsimp [exact_seq.π, exact_seq.ι] at *,
    apply_fun (λ i, kernel.ι f₄ i) at ht,
    simp only [← abelian.pseudoelement.comp_apply, kernel.lift_ι] at ht,
    simp at ht,
    have := e.extract 1 2,
    erw ← exact_iff_exact_seq at this,
    have := (@abelian.pseudoelement.pseudo_exact_of_exact
      _ _ _ _ _ _ _ _ this).2 _ ht,
    obtain ⟨a,ha⟩ := this,
    use cokernel.π f₁ a,
    rwa [← abelian.pseudoelement.comp_apply, cokernel.π_desc] }
end

lemma is_zero_of_exact_seq_of_is_iso_of_is_iso {X₁ X₂ X₃ X₄ X₅ : A}
  (f₁ : X₁ ⟶ X₂)
  (f₂ : X₂ ⟶ X₃)
  (f₃ : X₃ ⟶ X₄)
  (f₄ : X₄ ⟶ X₅)
  [epi f₁]
  [mono f₄]
  (e :  exact_seq A [f₁, f₂, f₃, f₄]) : is_zero X₃ :=
begin
  have h1 : is_zero (cokernel f₁) := is_zero_cokernel_of_epi f₁,
  have h2 : is_zero (kernel f₄) := is_zero_kernel_of_mono f₄,
  apply is_zero_of_exact_is_zero_is_zero _ _ _ h1 h2,
  exact (e.extract 0 2).π, exact (e.extract 2 3).ι,
  apply exact_seq.replace,
end

end category_theory
