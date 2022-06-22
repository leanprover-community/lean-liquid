import for_mathlib.homology
import for_mathlib.exact_lift_desc

noncomputable theory

open category_theory category_theory.limits opposite

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)

lemma homology.lift_desc (X Y Z : 𝓐) (f : X ⟶ Y) (g : Y ⟶ Z) (w)
  (U : 𝓐) (e : _ ⟶ U) (he : f ≫ e = 0) (V : 𝓐) (t : V ⟶ _) (ht : t ≫ g = 0) :
  homology.lift f g w (t ≫ cokernel.π _) (by simp [ht]) ≫
  homology.desc' _ _ _ (kernel.ι _ ≫ e) (by simp [he]) =
  t ≫ e :=
begin
  let s := _, change s ≫ _ = _,
  have hs : s = kernel.lift _ t ht ≫ homology.π' _ _ _,
  { apply homology.hom_to_ext,
    simp only [homology.lift_ι, category.assoc, homology.π'_ι, kernel.lift_ι_assoc] },
  simp [hs],
end

lemma homology.lift_desc' (X Y Z : 𝓐) (f : X ⟶ Y) (g : Y ⟶ Z) (w)
  (U : 𝓐) (e : Y ⟶ U) (he : f ≫ e = 0) (V : 𝓐) (t : V ⟶ Y) (ht : t ≫ g = 0)
  (u v) (hu : u = t ≫ cokernel.π _) (hv : v = kernel.ι _ ≫ e) :
  homology.lift f g w u (by simpa [hu]) ≫ homology.desc' _ _ _ v (by simpa [hv]) = t ≫ e :=
begin
  subst hu,
  subst hv,
  apply homology.lift_desc,
  assumption'
end
