import for_mathlib.derived.derived_cat
import for_mathlib.derived.example
import for_mathlib.short_exact
--import for_mathlib.random_homological_lemmas
--import for_mathlib.derived.Ext_lemmas

open category_theory category_theory.triangulated category_theory.limits

/-
WARNING!!!
this `sorry` below is probably not provable
`for_mathlib/derived/les2.lean` contains a different approach.
as soon as that file is sorry-free, we can nuke this file
-/

namespace homological_complex

section

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

end

variables {A : Type*} [category A] [abelian A] [enough_projectives A]
variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

open_locale pseudoelement
open category_theory.abelian

open_locale zero_object

-- WARNING!!! see WARNING below

def cone.π_quasi_iso (w : ∀ i, short_exact (f.f i) (g.f i)) :
  quasi_iso (cone.π f g (λ i, (w i).exact.w)) :=
{ is_iso := λ i, begin
    have w'' : ∀ i, f.f i ≫ g.f i = 0 := λ i, (w i).exact.w,
    let π := cone.π f g w'',
    have aux : ∀ n, short_exact ((kernel.ι π).f n) (π.f n) := λ n,
    { mono := equalizer.ι_mono,
      epi := by { haveI := (w n).epi, exact category_theory.epi_comp _ _},
      exact := exact_kernel_ι },
    let K := kernel π,
    suffices : ∀ n, is_zero (homology K n),
    { exact (six_term_exact_seq (kernel.ι π) π aux i (i+1) rfl).is_iso_of_zero_of_zero
        ((this _).eq_of_src _ _) ((this _).eq_of_tgt _ _), },
    intro n,
    obtain ⟨n, rfl⟩ : ∃ k, k+1 = n := ⟨n-1, sub_add_cancel _ _⟩,
    refine is_zero_of_iso_of_zero _
      (homology_iso K n (n+1) (n+1+1) rfl rfl).symm,
    apply exact.homology_is_zero,
    apply pseudoelement.exact_of_pseudo_exact,
    split, { intro a, rw [← pseudoelement.comp_apply, d_comp_d, pseudoelement.zero_apply], },
    intros b hb,
    set x := (kernel.ι π).f (n+1) b with xdef,
    have hx : π.f _ x = 0,
    { dsimp only [x, kernel.ι_f],
      rw [← pseudoelement.comp_apply, exact_kernel_ι.w, pseudoelement.zero_apply],
      apply_instance },
    let y := (biprod.snd : (X.X _) ⊞ (Y.X (n+1)) ⟶ Y.X (n+1)) x,
    have hy : g.f _ y = 0,
    { dsimp only [y], rw [← pseudoelement.comp_apply], exact hx },
    have w' := @pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _ (w (n+1)).exact,
    obtain ⟨a, ha⟩ := w'.2 y hy,
    let a' : ↥((X.X (n+1)) ⊞ (Y.X n)) := (biprod.inl : _ ⟶ (X.X (n+1)) ⊞ (Y.X n)) a,
    have ha' : π.f n a' = 0,
    { dsimp only [a', π, cone.π_f],
      rw [← pseudoelement.comp_apply, (exact_inl_snd (X.X (n+1)) _).w_assoc,
        zero_comp, pseudoelement.zero_apply], },
    have aux' := @pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _ (aux n).exact,
    obtain ⟨a'', ha''⟩ := aux'.2 a' ha',
    refine ⟨a'', _⟩,
    apply @pseudoelement.pseudo_injective_of_mono _ _ _ _ _ _ (aux (n+1)).mono,
    rw [← pseudoelement.comp_apply, ← (kernel.ι π).comm, pseudoelement.comp_apply, ha''],
    let φ : (cone f).X (n+1) ⟶ Y.X (n+1+1) ⊞ Y.X (n+1) :=
    biprod.lift (biprod.fst ≫ f.f _) biprod.snd,
    have hφ : mono φ,
    { haveI : mono (f.f (n+1+1)) := (w _).mono,
      constructor, intros Z α β H, dsimp [φ] at H,
      apply category_theory.limits.biprod.hom_ext,
      { rw ← cancel_mono (f.f (n+1+1)), apply_fun (λ ψ, ψ ≫ biprod.fst) at H,
        simpa only [category.assoc, biprod.lift_fst] using H, },
      { apply_fun (λ ψ, ψ ≫ biprod.snd) at H,
        simpa only [category.assoc, biprod.lift_snd] using H, } },
    apply_fun ⇑((kernel.ι π).f (n+1+1)) at hb,
    rw [← pseudoelement.comp_apply, ← (kernel.ι π).comm, pseudoelement.comp_apply,
      pseudoelement.apply_zero, ← xdef] at hb,
    dsimp only [cone_d, cone.d] at hb ⊢, rw [dif_pos rfl] at hb ⊢,
    change _ = x,
    simp only [X_eq_to_iso_refl, category.comp_id] at hb ⊢,
    simp only [← pseudoelement.comp_apply, category.assoc],

    /-
    simp only [biprod.lift_desc_comm, biprod.inl_desc] at hb ⊢,
    apply @pseudoelement.pseudo_injective_of_mono _ _ _ _ _ _ hφ,
    rw [← pseudoelement.comp_apply, biprod.comp_lift, biprod.lift_fst_assoc, biprod.lift_snd,
      ← category.comp_id (f.f (n+1)), preadditive.neg_comp, ← f.comm, ← preadditive.comp_neg,
      ← biprod.comp_lift, pseudoelement.comp_apply, ha, ← pseudoelement.comp_apply,
      biprod.comp_lift, category.comp_id],
    -- use `hb`

    WARNING!!!
    this sorry is probably not provable
    `for_mathlib/derived/les2.lean` contains a different approach.
    as soon as that file is sorry-free, we will nuke this lemma
    -/
    sorry
  end }

end homological_complex
