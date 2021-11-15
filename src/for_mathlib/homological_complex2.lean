import algebra.homology.homological_complex

open category_theory category_theory.limits

namespace homological_complex

variables {ι X 𝒜 : Type*} [category X] [category 𝒜] [has_zero_morphisms 𝒜] {c : complex_shape ι}

@[simps]
def functor_eval.obj (x : X) : homological_complex (X ⥤ 𝒜) c ⥤ homological_complex 𝒜 c :=
{ obj := λ C,
  { X := λ i, (C.X i).obj x,
    d := λ i j, (C.d i j).app x,
    shape' := λ i j hij, by rw [C.shape i j hij, zero_app],
    d_comp_d' := λ i j k hij hjk, by rw [← nat_trans.comp_app, C.d_comp_d, zero_app] },
  map := λ C D f,
  { f := λ i, (f.f i).app x,
    comm' := λ i j hij, by rw [← nat_trans.comp_app, ← nat_trans.comp_app, f.comm] } }
.

@[simps]
def functor_eval : X ⥤ homological_complex (X ⥤ 𝒜) c ⥤ homological_complex 𝒜 c :=
{ obj := λ x, functor_eval.obj x,
  map := λ x y f,
  { app := λ C,
    { f := λ i, (C.X i).map f,
      comm' := λ _ _ _, nat_trans.naturality _ _ },
    naturality' := λ _ _ _, by { ext i, symmetry, apply nat_trans.naturality } },
  map_id' := by { intros, ext, dsimp, rw [category_theory.functor.map_id], },
  map_comp' := by { intros, ext, dsimp, rw [category_theory.functor.map_comp], } }

end homological_complex
