import algebra.homology.homotopy

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [preadditive V]

section

variables {c : complex_shape ι} {C₁ C₂ C₃ : homological_complex V c}
variables {f g f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃}

-- namespace category_theory

@[simps]
def homotopy.of_eq (h : f = g) : homotopy f g :=
{ hom := 0,
  zero' := λ _ _ _, rfl,
  comm := by { intros, simp only [add_monoid_hom.map_zero, zero_add, h] } }

@[simps]
def homotopy.comp (h₁ : homotopy f₁ g₁) (h₂ : homotopy f₂ g₂) : homotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
(h₁.comp_right _).trans (h₂.comp_left _)

end

lemma d_next_nat (C D : chain_complex V ℕ) (i : ℕ) (f : Π i j, C.X i ⟶ D.X j) :
  d_next i f = C.d i (i-1) ≫ f (i-1) i :=
begin
  cases i,
  { dsimp [d_next],
    rcases (complex_shape.down ℕ).next 0 with _|⟨j,hj⟩;
    dsimp [d_next],
    { rw [C.shape, zero_comp], dsimp, dec_trivial },
    { dsimp at hj, exact (nat.succ_ne_zero _ hj).elim } },
  rw d_next_eq, dsimp, refl
end

lemma prev_d_nat (C D : cochain_complex V ℕ) (i : ℕ) (f : Π i j, C.X i ⟶ D.X j) :
  prev_d i f = f i (i-1) ≫ D.d (i-1) i :=
begin
  cases i,
  { dsimp [prev_d],
    rcases (complex_shape.up ℕ).prev 0 with _|⟨j,hj⟩;
    dsimp [prev_d],
    { rw [D.shape, comp_zero], dsimp, dec_trivial },
    { dsimp at hj, exact (nat.succ_ne_zero _ hj).elim } },
  rw prev_d_eq, dsimp, refl
end

-- end category_theory
