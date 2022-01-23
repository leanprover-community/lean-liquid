import for_mathlib.mapping_cone
import category_theory.triangulated.pretriangulated

noncomputable theory

universes v u

open_locale classical zero_object

open category_theory category_theory.limits category_theory.triangulated
open homological_complex

namespace homotopy_category

variables (V : Type u) [category.{v} V] [abelian V]

local notation `𝒦` := homotopy_category V (complex_shape.up ℤ)

def distinguished_triangles : set (triangle 𝒦) :=
λ T, ∃ (X Y Z : cochain_complex V ℤ) (f : X ⟶ Y) (g : Y ⟶ Z) h,
  nonempty (T ≅ triangleₕ_of_termwise_split f g h)

variable {V}
local notation `𝒦` := homotopy_category V (complex_shape.up ℤ)

lemma mem_distinguished_of_iso {T₁ T₂ : triangle 𝒦} (e : T₁ ≅ T₂)
  (hT : T₁ ∈ distinguished_triangles V) : T₂ ∈ distinguished_triangles V :=
⟨_, _, _, _, _, _,
  ⟨e.symm ≪≫ hT.some_spec.some_spec.some_spec.some_spec.some_spec.some_spec.some⟩⟩

lemma mem_distinguished_iff_exists_iso_cone (T : triangle 𝒦) :
  T ∈ distinguished_triangles V ↔ ∃ (X Y) (f : X ⟶ Y),
    nonempty (T ≅ (neg₃_functor _).obj (cone.triangleₕ f)) :=
begin
  split,
  { rintro ⟨X, Y, Z, f, g, h, ⟨e⟩⟩,
    refine ⟨_, _, f, ⟨e ≪≫ iso_cone_of_termwise_split f g h⟩⟩ },
  { rintro ⟨X, Y, f, ⟨e⟩⟩,
    refine ⟨_, _, _, _, _, _, ⟨e ≪≫ iso_termwise_split_of_cone f⟩⟩ }
end

lemma triangleₕ_of_termwise_split_mem_distinguished_triangles (X Y Z : cochain_complex V ℤ)
  (f : X ⟶ Y) (g : Y ⟶ Z) (h : ∀ i, splitting (f.f i) (g.f i)) :
    triangleₕ_of_termwise_split f g h ∈ distinguished_triangles V :=
⟨_, _, _, _, _, _, ⟨iso.refl _⟩⟩

lemma cone_triangeₕ_mem_distinguished_triangles (X Y Z : cochain_complex V ℤ)
  (f : X ⟶ Y) : (neg₃_functor _).obj (cone.triangleₕ f) ∈ distinguished_triangles V :=
(mem_distinguished_iff_exists_iso_cone _).mpr ⟨_, _, _, ⟨iso.refl _⟩⟩

lemma rotate_mem_distinguished_triangles (T : triangle 𝒦) (h : T ∈ distinguished_triangles V) :
  T.rotate ∈ distinguished_triangles V :=
begin
  obtain ⟨X, Y, f, ⟨e⟩⟩ := (mem_distinguished_iff_exists_iso_cone _).mp h,
  exact ⟨_, _, _, _, _, _, ⟨rotate.map_iso e ≪≫ neg₃_rotate.app _ ≪≫
    (triangle.nonneg_rotate_iso _).symm ≪≫
      (homotopy_category.lift_triangle _).map_iso (triangle_of_termwise_split_cone_iso f).symm⟩⟩,
end

def inv_rotate_lift_triangle (V : Type u) [category.{v} V] [abelian V] :
  inv_rotate ⋙ homotopy_category.lift_triangle V ≅
    homotopy_category.lift_triangle _ ⋙ inv_rotate :=
nat_iso.of_components (λ X, mk_triangle_iso (iso.refl _) (iso.refl _) (iso.refl _)
  (by { dsimp, simp only [category.comp_id, functor.map_neg, discrete.functor_map_id,
    category.id_comp, preadditive.comp_neg, shift_ε_inv_app, category.assoc, neg_inj,
    functor.map_comp, nat_trans.id_app, preadditive.neg_comp], erw category.id_comp })
  (by { dsimp, rw [category.comp_id, category.id_comp] })
  (by { dsimp, simp only [shift_ε_app, discrete.functor_map_id, category.id_comp,
    opaque_eq_to_iso_inv, category.assoc, functor.map_comp, nat_trans.id_app,
    category_theory.functor.map_id, unit_of_tensor_iso_unit_inv_app, shift_μ_inv_app],
    erw category.comp_id }))
  (by { intros, ext; exact (category.comp_id _).trans (category.id_comp _).symm })

lemma inv_rotate_mem_distinguished_triangles (T : triangle 𝒦) (h : T ∈ distinguished_triangles V) :
  T.inv_rotate ∈ distinguished_triangles V :=
begin
  obtain ⟨X, Y, Z, f, g, h, ⟨e⟩⟩ := h,
  exact (mem_distinguished_iff_exists_iso_cone _).mpr ⟨_, _, _,
    ⟨inv_rotate.map_iso e ≪≫ ((inv_rotate_lift_triangle _).app _).symm ≪≫
    (homotopy_category.lift_triangle _).map_iso ((neg₃_equiv _).iso_equiv _ _
    ((triangle.nonneg_inv_rotate_iso _).symm ≪≫ inv_rotate_iso_cone_triangle f g h))⟩⟩
end

instance : pretriangulated 𝒦 :=
{ distinguished_triangles := distinguished_triangles V,
  isomorphic_distinguished := sorry,
  contractible_distinguished := begin
    rintro ⟨X⟩,
    use [X, X, 0, 𝟙 _, 0, λ i, (splitting_of_is_iso_zero (𝟙 (X.X i)) : _)],
    refine ⟨mk_triangle_iso (iso.refl _) (iso.refl _) (iso.refl _) _ _ _⟩; dsimp; simp; refl
  end,
  distinguished_cocone_triangle := begin
    rintros ⟨X⟩ ⟨Y⟩ f,
    induction f using quot.induction_on,
    exact ⟨_, _, _, _, _, _, _, _, _, ⟨iso_termwise_split_of_cone f⟩⟩,
  end,
  rotate_distinguished_triangle := begin
    intro T,
    split,
    { apply rotate_mem_distinguished_triangles },
    { intro h,
      exact mem_distinguished_of_iso (triangle_rotation.unit_iso.app T).symm
        (inv_rotate_mem_distinguished_triangles _ h) }
  end,
  complete_distinguished_triangle_morphism := begin
    intros,
    obtain ⟨X₁, Y₁, f₁, ⟨e₁⟩⟩ := (mem_distinguished_iff_exists_iso_cone _).mp h₁,
    obtain ⟨X₂, Y₂, f₂, ⟨e₂⟩⟩ := (mem_distinguished_iff_exists_iso_cone _).mp h₂,
    let h : homotopy (f₁ ≫ quot.out (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂))
      (quot.out (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁) ≫ f₂),
    { apply homotopy_of_eq,
      simp only [quotient_map_out, category.assoc, functor.map_comp],
      erw [← e₂.hom.comm₁, reassoc_of e₁.inv.comm₁, reassoc_of comm₁] },
    refine ⟨e₁.hom.hom₃ ≫ (quotient V _).map (cone.map h) ≫ e₂.inv.hom₃, _, _⟩,
    { rw [reassoc_of e₁.hom.comm₂, ← is_iso.eq_inv_comp],
      simp_rw ← category.assoc,
      rw [← is_iso.eq_comp_inv, ← inv_hom₃, ← inv_hom₂, is_iso.iso.inv_inv, is_iso.iso.inv_hom],
      simp_rw category.assoc,
      rw [e₂.hom.comm₂],
      convert (cone.triangleₕ_map h).comm₂ using 1,
      dsimp, simp },
    { simp_rw category.assoc,
      rw [← is_iso.inv_comp_eq, ← inv_hom₃, is_iso.iso.inv_hom, ← reassoc_of e₁.inv.comm₃,
        ← e₂.inv.comm₃],
      dsimp,
      have := (cone.triangleₕ_map h).comm₃,
      dsimp at this,
      rw [← homotopy_category.quotient_map_shift, quotient_map_out] at this,
      simp only [preadditive.neg_comp_assoc, preadditive.comp_neg, category.assoc, neg_inj,
        preadditive.neg_comp],
      rw [← reassoc_of this, ← functor.map_comp, ← functor.map_comp],
      congr' 2,
      rw [← is_iso.comp_inv_eq, ← inv_hom₁, is_iso.iso.inv_inv, category.assoc] }
  end }

end homotopy_category
