import category_theory.triangulated.pretriangulated
import category_theory.abelian.exact
import category_theory.linear.yoneda
import algebra.category.Module.abelian
import algebra.category.Group.abelian
import category_theory.currying
import for_mathlib.exact_seq
import for_mathlib.preadditive_yoneda
import for_mathlib.AddCommGroup.exact

import category_theory.abelian.diagram_lemmas.four

namespace category_theory.triangulated

open category_theory
open category_theory.limits
open pretriangulated

universes v u
variables {C : Type u} [category.{v} C] [preadditive C]

-- Move me
instance preadditive_yoneda_flip_additive (X : C) :
  (preadditive_yoneda.flip.obj (opposite.op X)).additive :=
by { fsplit, dsimp, intros, ext1, apply preadditive.comp_add }

variables {R : Type*} [ring R] [linear R C]

-- Move me
instance linear_yoneda_flip_additive (X : C) :
  ((linear_yoneda R C).flip.obj (opposite.op X)).additive :=
by { fsplit, dsimp, intros, ext1, dsimp, apply preadditive.comp_add }

variables [has_zero_object C] [has_shift C ℤ] [∀ (n : ℤ), (shift_functor C n).additive]
  [pretriangulated C]

/-- A functor `F` is a *homological* functor if for every distinguished triangle
`A ⟶ B ⟶ C ⟶ A[1]` the sequence `F(A) ⟶ F(B) ⟶ F(C)` is exact. -/
class homological_functor {A : Type*} [category A] [abelian A] (F : C ⥤ A) [F.additive] : Prop :=
(cond [] : ∀ (T : triangle C) (hT : T ∈ dist_triang C), exact (F.map T.mor₁) (F.map T.mor₂))

lemma four_term_exact_seq {A : Type*} [category A] [abelian A] (F : C ⥤ A) [F.additive]
  [homological_functor F] (T : triangle C) (hT : T ∈ dist_triang C):
  exact_seq A [F.map T.mor₁, F.map T.mor₂, F.map T.mor₃] :=
begin
  apply exact_seq.cons,
  apply homological_functor.cond F _ hT,
  rw ← exact_iff_exact_seq,
  apply homological_functor.cond F _ ((rotate_distinguished_triangle T).mp hT),
end

lemma five_term_exact_seq {A : Type*} [category A] [abelian A] (F : C ⥤ A) [F.additive]
  [homological_functor F] (T : triangle C) (hT : T ∈ dist_triang C):
  exact_seq A [F.map T.inv_rotate.mor₁, F.map T.mor₁, F.map T.mor₂, F.map T.mor₃] :=
begin
  apply exact_seq.cons _ _ _ _ (four_term_exact_seq F _ hT),
  apply homological_functor.cond F,
  apply inv_rot_of_dist_triangle _ _ hT,
end

lemma complete_distinguished_triangle_morphism'
  (T₁ T₂ : triangle C)
  (h₁ : T₁ ∈ dist_triang C)
  (h₂ : T₂ ∈ dist_triang C)
  (f₂ : T₁.obj₂ ⟶ T₂.obj₂)
  (f₃ : T₁.obj₃ ⟶ T₂.obj₃)
  (w : T₁.mor₂ ≫ f₃ = f₂ ≫ T₂.mor₂) :
  ∃ f₁ : T₁.obj₁ ⟶ T₂.obj₁, (T₁.mor₁ ≫ f₂ = f₁ ≫ T₂.mor₁) ∧ (T₁.mor₃ ≫ f₁⟦1⟧' = f₃ ≫ T₂.mor₃) :=
begin
  let T₁' := T₁.rotate,
  let T₂' := T₂.rotate,
  obtain ⟨g,h1,h2⟩ := complete_distinguished_triangle_morphism T₁' T₂' _ _ f₂ f₃ w,
  use (shift_shift_neg _ _).inv ≫ g⟦(-1 : ℤ)⟧' ≫ (shift_shift_neg _ _).hom,
  split,
  { dsimp at h2,
    apply_fun (λ e, - (shift_functor C (-1 : ℤ)).map e ≫ (shift_shift_neg _ _).hom) at h2,
    simp only [category.assoc, functor.map_comp] at ⊢ h2,
    rw iso.eq_inv_comp,
    convert h2 using 1,
    { simp },
    { simp } },
  { convert h1 using 1,
    congr' 1,
    simp only [functor.map_comp, category.assoc],
    rw shift_neg_shift',
    simp only [category.assoc, ← functor.map_iso_inv, ← functor.map_iso_hom],
    have : (shift_functor C 1).map_iso (shift_shift_neg T₂.obj₁ 1) =
      shift_neg_shift T₂'.obj₃ 1, by { dsimp, simp }, rw this, clear this,
    have : (shift_functor C 1).map_iso (shift_shift_neg T₁.obj₁ (1 : ℤ)) =
      shift_neg_shift ((shift_functor C (1 : ℤ)).obj T₁.obj₁) (1 : ℤ),
      by simp, rw this, clear this,
    simp only [iso.inv_hom_id, iso.inv_hom_id_assoc, category.id_comp, category.comp_id] },
  { rw ← rotate_distinguished_triangle, exact h₁ },
  { rw ← rotate_distinguished_triangle, exact h₂ }
end

theorem dist_triang_to_exact_complex
  (T : triangle C)
  (hT : T ∈ dist_triang C)
  (X : C)
  (f : X ⟶ T.obj₂)
  (hf : f ≫ T.mor₂ = 0) :
  ∃ g : X ⟶ T.obj₁, g ≫ T.mor₁ = f :=
begin
  let I : triangle C := contractible_triangle C X,
  obtain ⟨f₁,h₁,h₂⟩ :=
    complete_distinguished_triangle_morphism' I T
    (contractible_distinguished _) hT f 0
    (by simpa using hf.symm),
  use f₁,
  rw ← h₁,
  dsimp,
  simp,
end

instance preadditive_yoneda_flip_homological (X : C) :
  homological_functor (preadditive_yoneda.flip.obj (opposite.op X)) :=
begin
  constructor,
  intros T hT,
  suffices : add_monoid_hom.range ((preadditive_yoneda.flip.obj (opposite.op X)).map T.mor₁) =
    add_monoid_hom.ker ((preadditive_yoneda.flip.obj (opposite.op X)).map T.mor₂),
  { rwa AddCommGroup.exact_iff },
  apply le_antisymm,
  { rintros _ ⟨(g : X ⟶ _),rfl⟩,
    dsimp,
    obtain ⟨e,h1,he⟩ := complete_distinguished_triangle_morphism
      (contractible_triangle _ X) T (contractible_distinguished _) hT g (g ≫ T.mor₁)
      (by { dsimp, simp }),
    dsimp at he,
    simp only [zero_comp] at he,
    change _ = _,
    simp [← h1] },
  { rintros (f : X ⟶ _) (hf : f ≫ _ = 0),
    apply dist_triang_to_exact_complex _ hT _ _ hf }
end

-- Prove this using the above theorem.
instance linear_yoneda_flip_homological (X : C) :
  homological_functor ((linear_yoneda R C).flip.obj (opposite.op X)) :=
begin
  constructor,
  intros T hT,
  rw Module.exact_iff,
  apply le_antisymm,
  { rintros _ ⟨(g : X ⟶ _),rfl⟩,
    dsimp,
    obtain ⟨e,h1,he⟩ := complete_distinguished_triangle_morphism
      (contractible_triangle _ X) T (contractible_distinguished _) hT g (g ≫ T.mor₁)
      (by { dsimp, simp }),
    dsimp at he,
    simp only [zero_comp] at he,
    simp [← h1] },
  { rintros (f : X ⟶ _) (hf : f ≫ _ = 0),
    apply dist_triang_to_exact_complex _ hT _ _ hf }
end

lemma is_iso_triangle_hom_of_is_iso (T₁ T₂ : triangle C)
  (e : T₁ ⟶ T₂)
  [is_iso e.hom₁]
  [is_iso e.hom₂]
  [is_iso e.hom₃] : is_iso e :=
begin
  constructor,
  refine ⟨⟨inv e.hom₁, inv e.hom₂, inv e.hom₃, _, _⟩, _, _⟩,
  { dsimp,
    rw [is_iso.comp_inv_eq, category.assoc, is_iso.eq_inv_comp, e.comm₁] },
  { dsimp,
    rw [is_iso.comp_inv_eq, category.assoc, is_iso.eq_inv_comp, e.comm₂] },
  { ext; dsimp; simp },
  { ext; dsimp; simp },
end

lemma is_iso_of_is_iso_rotate (T₁ T₂ : triangle C)
  (e : T₁ ⟶ T₂) [h : is_iso (rotate.map e)] : is_iso e :=
begin
  haveI : is_iso (triangle_rotation.functor.map e) := h,
  apply is_iso_of_fully_faithful (triangle_rotation.functor : triangle C ⥤ triangle C),
end

lemma is_iso_of_is_iso_inv_rotate (T₁ T₂ : triangle C)
  (e : T₁ ⟶ T₂) [h : is_iso (inv_rotate.map e)] : is_iso e :=
begin
  haveI : is_iso (triangle_rotation.inverse.map e) := h,
  apply is_iso_of_fully_faithful (triangle_rotation.inverse : triangle C ⥤ triangle C),
end

theorem is_iso_of_is_iso_of_is_iso (T₁ T₂ : triangle C)
  (h₁ : T₁ ∈ dist_triang C) (h₂ : T₂ ∈ dist_triang C)
  (e : T₁ ⟶ T₂) [is_iso e.hom₁] [is_iso e.hom₃] : is_iso e :=
begin
  apply_with is_iso_triangle_hom_of_is_iso { instances := ff },
  any_goals { apply_instance },
  apply_instance,

  apply_with is_iso_of_is_iso_preadditive_yoneda_map_app { instances := ff },
  swap, apply_instance,
  intros W,

  let Y := (preadditive_yoneda.flip.obj (opposite.op W)),

  have H1 := five_term_exact_seq Y _ h₁,
  have H2 := five_term_exact_seq Y _ h₂,

  have sq1 := e.inv_rotate.comm₁,
  apply_fun (λ e, Y.map e) at sq1,
  simp only [functor.map_comp] at sq1,

  have sq2 := e.comm₁,
  apply_fun (λ e, Y.map e) at sq2,
  simp only [functor.map_comp] at sq2,

  have sq3 := e.comm₂,
  apply_fun (λ e, Y.map e) at sq3,
  simp only [functor.map_comp] at sq3,

  have sq4 := e.comm₃,
  apply_fun (λ e, Y.map e) at sq4,
  simp only [functor.map_comp] at sq4,

  haveI : is_iso (Y.map (triangulated.triangle_morphism.inv_rotate e).hom₁),
  { dsimp only [triangulated.triangle_morphism.inv_rotate],
    rw ← functor.comp_map,
    apply functor.map_is_iso },

  haveI : is_iso (Y.map (triangulated.triangle_morphism.inv_rotate e).hom₂),
  { dsimp only [triangulated.triangle_morphism.inv_rotate],
    apply functor.map_is_iso },

  haveI : is_iso (Y.map e.hom₃),
  { apply functor.map_is_iso },

  haveI : is_iso (Y.map ((shift_functor C (1 : ℤ)).map e.hom₁)),
  { rw ← functor.comp_map,
    apply functor.map_is_iso },

  exact @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    sq1.symm sq2.symm sq3.symm _ _ _ _ _ sq4.symm
    ((exact_iff_exact_seq _ _).mpr (H1.extract 0 2))
    ((exact_iff_exact_seq _ _).mpr (H1.extract 1 2))
    ((exact_iff_exact_seq _ _).mpr (H1.extract 2 3))
    ((exact_iff_exact_seq _ _).mpr (H2.extract 0 2))
    ((exact_iff_exact_seq _ _).mpr (H2.extract 1 2))
    ((exact_iff_exact_seq _ _).mpr (H2.extract 2 3)) _ _ _ _,
end

lemma is_iso_of_is_iso_of_is_iso' (T₁ T₂ : triangle C)
  (h₁ : T₁ ∈ dist_triang C) (h₂ : T₂ ∈ dist_triang C)
  (e : T₁ ⟶ T₂) [h1 : is_iso e.hom₁] [h2 : is_iso e.hom₂] : is_iso e :=
begin
  suffices : is_iso (rotate.map e),
  { resetI, apply is_iso_of_is_iso_rotate },
  haveI : is_iso (rotate.map e).hom₁ := h2,
  haveI : is_iso (rotate.map e).hom₃,
  { apply functor.map_is_iso },
  apply is_iso_of_is_iso_of_is_iso,
  all_goals { erw ← rotate_distinguished_triangle, assumption },
end

end category_theory.triangulated
