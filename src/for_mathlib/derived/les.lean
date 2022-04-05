import for_mathlib.derived.derived_cat
import for_mathlib.derived.example

open category_theory category_theory.triangulated category_theory.limits

namespace category_theory

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]

-- move me
lemma exact_seq.is_iso_of_zero_of_zero {A B C D : 𝓐} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
  {L : list (arrow 𝓐)} (H : exact_seq 𝓐 (f :: g :: h :: L)) (hf : f = 0) (hh : h = 0) :
  is_iso g :=
begin
  subst f, subst h,
  have : mono g, { rw [H.pair.mono_iff_eq_zero], },
  haveI : epi g, { rw [(H.drop 1).pair.epi_iff_eq_zero] },
  exact is_iso_of_mono_of_epi g,
end

end category_theory

variables (A : Type*) [category A] [abelian A] [enough_projectives A]

namespace bounded_derived_category

@[simps]
def forget : bounded_derived_category A ⥤ bounded_homotopy_category A :=
{ obj := λ X, X.val,
  map := λ _ _ f, f.val,
  map_id' := λ _ , rfl,
  map_comp' := λ _ _ _ _ _, rfl }

instance Ext_additive_fst (i : ℤ) (X : bounded_derived_category A) :
  (((Ext A i).flip.obj X).right_op).additive :=
{ map_add' := begin
    intros Y Z f g, dsimp,
    conv_rhs { rw ← op_add }, congr' 1, ext e,
    dsimp, rw preadditive.add_comp,
  end }

instance Ext_homological_fst (i : ℤ) (X : bounded_derived_category A) :
  homological_functor ((Ext A i).flip.obj X).right_op :=
category_theory.triangulated.preadditive_yoneda_op_homological (X⟦i⟧)

end bounded_derived_category

namespace homological_complex

variables {A}
variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

noncomputable
def cone.π (w : ∀ i, f.f i ≫ g.f i = 0) :
  cone f ⟶ Z :=
{ f := λ i, biprod.snd ≫ g.f i,
  comm' := λ i j hij, begin
    dsimp at hij, subst j, dsimp [cone.d], rw [if_pos rfl, biprod.lift_snd_assoc],
    ext,
    { simp only [exact.w_assoc, zero_comp, category.assoc, biprod.inl_desc_assoc,
        category.id_comp, w], },
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

noncomputable def kernel.ι : kernel f ⟶ X :=
{ f := λ i, kernel.ι _,
  comm' := λ i j hij, by simp only [kernel_d, kernel.lift_ι] }

open_locale pseudoelement

def cone.π_quasi_iso (w : ∀ i, short_exact (f.f i) (g.f i)) :
  quasi_iso (cone.π f g (λ i, (w i).exact.w)) :=
{ is_iso := λ i, begin
    let π := cone.π f g (λ i, (w i).exact.w),
    have aux : ∀ n, short_exact ((kernel.ι π).f n) (π.f n),
    { sorry },
    suffices : ∀ n, is_zero (homology (kernel π) n),
    { exact (six_term_exact_seq (kernel.ι π) π aux i (i+1) rfl).is_iso_of_zero_of_zero
        ((this _).eq_of_src _ _) ((this _).eq_of_tgt _ _), },
    intro n,
    refine is_zero_of_iso_of_zero _
      (homology_iso (kernel π) (n-1) n (n+1) (sub_add_cancel _ _) rfl).symm,
    apply is_zero_homology_of_exact,
    rw [abelian.exact_iff, d_comp_d, eq_self_iff_true, true_and],
    apply abelian.pseudoelement.zero_morphism_ext,
    intro a,
    sorry
  end }

end homological_complex
