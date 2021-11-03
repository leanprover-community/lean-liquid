import for_mathlib.sheafification.plus
import for_mathlib.sheafification.multifork

namespace category_theory

namespace presheaf

open category_theory.limits opposite

universes w v u
variables {C : Type u} [category.{v} C] {D : Type w} [category.{max v u} D]
  {J : grothendieck_topology C} {P : Cᵒᵖ ⥤ D}

noncomputable theory

def is_sheaf.glue {X : C} {S : sieve X} {E : D} (hS : S ∈ J X) (h : is_sheaf J P)
  (x : presieve.family_of_elements (P ⋙ coyoneda.obj (op E)) S)
  (hx : x.compatible) : E ⟶ P.obj (op X) :=
(h E S hS x hx).some

@[simp]
lemma is_sheaf.glue_map {X Y : C} {S : sieve X} {E : D} (hS : S ∈ J X)
  (f : Y ⟶ X) (hf : S f) (h : is_sheaf J P)
  (x : presieve.family_of_elements (P ⋙ coyoneda.obj (op E)) S)
  (hx : x.compatible) : h.glue hS x hx ≫ P.map f.op = x f hf :=
(h E S hS x hx).some_spec.1 _ _

lemma is_sheaf.hom_ext {X : C} {S : sieve X} {E : D} (hS : S ∈ J X)
  (h : is_sheaf J P) (a b : E ⟶ P.obj (op X))
  (w : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : S f), a ≫ P.map f.op = b ≫ P.map f.op) : a = b :=
begin
  let x : presieve.family_of_elements (P ⋙ coyoneda.obj (op E)) S :=
    λ Y f hf, a ≫ P.map f.op,
  have hx : x.compatible,
  { intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ ww,
    dsimp [x],
    simp only [category.assoc, ← P.map_comp, ← op_comp, ww] },
  have ha : a = h.glue hS x hx,
  { apply (h E S hS x hx).some_spec.2,
    dsimp [presieve.family_of_elements.is_amalgamation],
    intros,
    dsimp [x],
    refl },
  have hb : b = h.glue hS x hx,
  { apply (h E S hS x hx).some_spec.2,
    dsimp [presieve.family_of_elements.is_amalgamation],
    intros,
    dsimp [x],
    symmetry,
    apply w,
    assumption },
  rw [ha, ← hb],
end

def is_limit_of_is_sheaf {X : C} (S : J.cover X)
  (h : is_sheaf J P) :
  is_limit (S.multifork P) :=
{ lift := λ E, h.glue S.condition (S.family_of_elements P E) (S.compatible P E),
  fac' := begin
    rintros (K : multifork _) (a|b),
    { convert is_sheaf.glue_map S.condition a.f a.hf h _ _,
      tidy },
    { rw ← K.w (walking_multipair.hom.fst b),
      rw ← (S.multifork P).w (walking_multipair.hom.fst b),
      simp_rw ← category.assoc,
      congr' 1,
      exact is_sheaf.glue_map S.condition _ _ h _ _ }
  end,
  uniq' := begin
    rintros (K : multifork _) m hh,
    apply is_sheaf.hom_ext S.condition h,
    intros Y f hf,
    specialize hh (walking_multipair.zero ⟨Y,f,hf⟩),
    erw hh,
    erw is_sheaf.glue_map S.condition f hf,
    refl,
  end }

theorem is_sheaf_iff_multifork : presheaf.is_sheaf J P ↔ ∀ (X : C) (S : J.cover X),
  nonempty (is_limit (S.multifork P)) :=
begin
  split,
  { intros hP X S,
    refine ⟨is_limit_of_is_sheaf _ hP⟩ },
  { intros h E X S hS x hx,
    let T : J.cover X := ⟨S,hS⟩,
    specialize h X T,
    obtain ⟨h⟩ := h,
    let K : multifork (T.index P) :=
      multifork.of_ι _ E (λ a, x a.f a.hf) (λ b, hx _ _ _ _ b.w),
    let t := h.lift K,
    use t,
    split,
    { dsimp,
      intros Y f hf,
      dsimp,
      apply h.fac (K) (walking_multipair.zero ⟨Y,f,hf⟩) },
    { intros y hy,
      dsimp [t],
      apply h.uniq K,
      rintros (a|b),
      { apply hy },
      { rw ← K.w (walking_multipair.hom.fst b),
        rw ← (T.multifork P).w (walking_multipair.hom.fst b),
        simp_rw ← category.assoc,
        congr' 1,
        apply hy } } }
end

end presheaf

end category_theory
