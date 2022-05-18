import for_mathlib.commsq
import for_mathlib.les_homology
import for_mathlib.AddCommGroup.pt
import for_mathlib.bicartesian3
import for_mathlib.abelian_sheaves.functor_category

import system_of_complexes.shift_sub_id
import pseudo_normed_group.system_of_complexes2

noncomputable theory

universes u

open_locale nnreal

open opposite category_theory category_theory.limits category_theory.preadditive

section step1

variables {A B C : ℝ≥0ᵒᵖ ⥤ Ab.{u}} (f : A ⟶ B)
variables (ι : ulift.{u} ℕ → ℝ≥0)

def shift_sub_id.commsq (hι : monotone ι) :
  commsq (shift_sub_id A ι hι)
    (pi.map $ λ _, f.app _) (pi.map $ λ _, f.app _)
         (shift_sub_id B ι hι) :=
commsq.of_eq
begin
  simp only [shift_sub_id, sub_comp, comp_sub, category.id_comp, category.comp_id, shift_sub_id.shift],
  congr' 1,
  apply limit.hom_ext,
  intro j,
  simp only [limit.lift_map, limit.lift_π, cones.postcompose_obj_π, nat_trans.comp_app,
    fan.mk_π_app, discrete.nat_trans_app, category.assoc, nat_trans.naturality, lim_map_π_assoc],
end

end step1

section step2

variables {A B C : ulift.{u} ℕ → Ab.{u}} (f : Π k, A k ⟶ B k) (g : Π k, B k ⟶ C k)

lemma pi_map_exact (H : ∀ k, exact (f k) (g k)) :
  exact (pi.map f) (pi.map g) :=
begin
  simp only [AddCommGroup.exact_iff'] at H ⊢,
  split,
  { apply limit.hom_ext, intro j,
    simp only [category.assoc, lim_map_π, discrete.nat_trans_app, lim_map_π_assoc,
      zero_comp, (H j).1, comp_zero], },
  intros x hx,
  rw [add_monoid_hom.mem_ker, Ab.apply_eq_zero] at hx,
  have : ∀ k, (Ab.pt (limit.π (discrete.functor (λ k, B k)) k x)) ≫ g k = 0,
  { intro k,
    suffices : Ab.pt x ≫ pi.map g ≫ pi.π _ k = 0,
    { simpa only [lim_map_π, discrete.nat_trans_app, ← category.assoc, hx, Ab.pt_comp] },
    rw [← category.assoc, hx, zero_comp] },
  simp only [← Ab.apply_eq_zero] at this,
  replace := λ k, (H k).2 (this k),
  choose y hy using this,
  refine ⟨pi.lift (λ k, Ab.pt (y k)) ⟨1⟩, _⟩,
  rw [← category_theory.comp_apply, ← Ab.pt_apply' x],
  congr' 1,
  apply limit.hom_ext,
  intro j,
  simp only [limit.lift_map, limit.lift_π, cones.postcompose_obj_π, nat_trans.comp_app,
    fan.mk_π_app, discrete.nat_trans_app, Ab.pt_comp, hy],
end

end step2

section step3

variables {A B C : ℝ≥0ᵒᵖ ⥤ cochain_complex Ab.{u} ℕ} (f : A ⟶ B) (g : B ⟶ C)
variables (ι : ulift.{u} ℕ → ℝ≥0) (n : ℕ)

def piH_hom :
  (∏ (λ x, (A.obj (op $ ι x)).homology n)) ⟶ (∏ (λ x, (B.obj (op $ ι x)).homology n)) :=
pi.map $ λ k, (homology_functor _ _ _).map $ f.app _

def shift_sub_id.δ (H : ∀ c n, short_exact ((f.app c).f n) ((g.app c).f n)) :
  C ⋙ homology_functor _ _ n ⟶ A ⋙ homology_functor _ _ (n+1) :=
{ app := λ c, homological_complex.δ (f.app _) (g.app _) (H _) _ _ rfl,
  naturality' := λ c₁ c₂ h, begin
    sorry -- this one might be tricky
  end }

def piδ (H : ∀ c n, short_exact ((f.app c).f n) ((g.app c).f n)) :
  (∏ (λ x, (C.obj (op $ ι x)).homology n)) ⟶ (∏ (λ x, (A.obj (op $ ι x)).homology (n+1))) :=
pi.map $ λ k, (shift_sub_id.δ _ _ _ H).app _

lemma piH_les (H : ∀ c n, short_exact ((f.app c).f n) ((g.app c).f n)) :
  exact_seq Ab.{u} [piH_hom f ι n, piH_hom g ι n, piδ f g ι n H] :=
begin
  apply exact.cons,
  { apply pi_map_exact, intro k,
    have := homological_complex.six_term_exact_seq _ _ (H (op $ ι k)) n (n+1) rfl,
    exact this.pair, },
  apply exact.exact_seq,
  { apply pi_map_exact, intro k,
    have := homological_complex.six_term_exact_seq _ _ (H (op $ ι k)) n (n+1) rfl,
    exact (this.drop 1).pair, },
end

end step3

section step4

lemma bicartesian_of_aut_of_end_of_end_of_aut
  {A B C D : Ab.{u}} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
  {α : A ⟶ A} {β : B ⟶ B} {γ : C ⟶ C} {δ : D ⟶ D}
  (H : exact_seq Ab.{u} [f, g, h])
  (sq1 : commsq f α β f) (sq2 : commsq g β γ g) (sq3 : commsq h γ δ h)
  [is_iso α] [is_iso δ] :
  sq2.bicartesian :=
begin
  have aux : _ := _,
  rw commsq.bicartesian_iff_isos _ _ aux aux sq2.kernel sq2 sq2.cokernel,
  swap,
  { apply exact.cons, { exact exact_kernel_ι },
    apply exact.exact_seq, { apply abelian.exact_cokernel } },
  sorry
  -- use (important!) the fact that we have a `kernel.map` (resp. `cokernel.map`)
  -- arising between two identical exact sequences
end

end step4

section step5

variables {A B C : system_of_complexes.{u}} (f : A.to_Ab ⟶ B.to_Ab) (g : B.to_Ab ⟶ C.to_Ab)
variables (n : ℕ) (ι : ulift.{u} ℕ → ℝ≥0) (hι : monotone ι)

lemma shift_sub_id.bicartesian
  (HA₁ : is_iso (shift_sub_id (A.to_AbH n) ι hι))
  (HA₂ : is_iso (shift_sub_id (A.to_AbH (n+1)) ι hι))
  (H : ∀ c n, short_exact ((f.app c).f n) ((g.app c).f n)) :
  (@shift_sub_id.commsq (B.to_AbH n) (C.to_AbH n)
    (whisker_right g _) ι hι).bicartesian :=
begin
  rw ← commsq.bicartesian.symm_iff,
  let S1 := ((@shift_sub_id.commsq (A.to_AbH n) (B.to_AbH n) (whisker_right f _) ι hι)).symm,
  let S2 := ((@shift_sub_id.commsq (B.to_AbH n) (C.to_AbH n) (whisker_right g _) ι hι)).symm,
  let S3 := ((@shift_sub_id.commsq (C.to_AbH n) (A.to_AbH (n+1)) (shift_sub_id.δ _ _ _ H) ι hι)).symm,
  convert bicartesian_of_aut_of_end_of_end_of_aut (piH_les _ _ _ _ _) S1 S2 S3,
end

end step5

section step6

variables {A B A' B' : ℝ≥0ᵒᵖ ⥤ Ab.{u}} (f : A ⟶ B) (f' : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B')
variables (ι : ulift.{u} ℕ → ℝ≥0) (hι : monotone ι)

lemma shift_sub_id.bicartesian_iso (w : f ≫ eB.hom = eA.hom ≫ f')
  (sq : (shift_sub_id.commsq f ι hι).bicartesian) :
  (shift_sub_id.commsq f' ι hι).bicartesian :=
begin
  let H : _ := _,
  apply commsq.bicartesian.of_iso _ _ _ _ _ H H _ sq,
  { refine limits.lim.map_iso (discrete.nat_iso $ λ k, eA.app _), },
  { refine limits.lim.map_iso (discrete.nat_iso $ λ k, eB.app _), },
  { apply shift_sub_id.commsq },
  { apply shift_sub_id.commsq },
  { apply commsq.of_eq, delta pi.map,
    simp only [functor.map_iso_hom, ← lim_map_eq_lim_map, ← category_theory.functor.map_comp],
    apply limit.hom_ext,
    simp only [lim_map_eq_lim_map, lim_map_π, nat_trans.comp_app, discrete.nat_trans_app,
      discrete.nat_iso_hom_app, iso.app_hom],
    intro, simp only [← nat_trans.comp_app, w], }
end


end step6
