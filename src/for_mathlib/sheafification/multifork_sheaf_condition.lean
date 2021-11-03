import for_mathlib.sheafification.plus
import for_mathlib.sheafification.multifork

namespace category_theory

namespace presheaf

open category_theory.limits opposite

universes w v u
variables {C : Type u} [category.{v} C] {D : Type w} [category.{max v u} D]
  (J : grothendieck_topology C) (P : Cᵒᵖ ⥤ D)

def is_limit_of_is_sheaf_for {X : C} (S : J.cover X)
  (h : presieve.is_sheaf_for (P ⋙ coyoneda.obj (op (P.obj (op X)))) S) :
  is_limit (S.multifork P) :=
{ lift := λ E, begin
    dsimp [grothendieck_topology.cover.multifork],
    dsimp [presieve.is_sheaf_for] at h,
    let x : presieve.family_of_elements (P ⋙ coyoneda.obj (op (P.obj (op X)))) S :=
      λ (Y : C) (f : Y ⟶ X) (hf : S f), (E.π.app (walking_multipair.zero (⟨Y,f,hf⟩ : S.left)),

  end,
  fac' := _,
  uniq' := _ }

theorem is_sheaf_iff_multifork : presheaf.is_sheaf J P ↔ ∀ (X : C) (S : J.cover X),
  nonempty (is_limit
  $ multifork.of_ι S.fst S.snd
    (λ I, P.obj (op I.Y))
    (λ I, P.obj (op I.Z))
    (λ I, P.map I.g₁.op) (λ I, P.map I.g₂.op)
    (P.obj (op X))
    (λ I, P.map I.f.op)
    begin
      intros I,
      simp_rw [← P.map_comp, ← op_comp],
      congr' 2,
      exact I.w,
    end) :=
begin
  split,
  { intros hP,
    intros X S,
    specialize hP (P.obj (op X)) (S : sieve X) S.condition,
  },
  { sorry }
end

end presheaf

end category_theory
