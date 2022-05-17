import for_mathlib.commsq
import for_mathlib.les_homology
import for_mathlib.AddCommGroup.pt
import for_mathlib.bicartesian3

import system_of_complexes.shift_sub_id
import pseudo_normed_group.system_of_complexes2

noncomputable theory

universes u

open_locale nnreal

open opposite category_theory category_theory.limits category_theory.preadditive

section step1

variables {A B C : ℝ≥0ᵒᵖ ⥤ Ab.{u}} (f : A ⟶ B)
variables (ι : ℕ → ℝ≥0)

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

variables {A B C : ℕ → Ab.{u}} (f : Π k, A k ⟶ B k) (g : Π k, B k ⟶ C k)

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
  have : ∀ (k : ℕ), (Ab.pt (limit.π (discrete.functor (λ (k : ℕ), B k)) k x)) ≫ g k = 0,
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
variables (ι : ℕ → ℝ≥0) (n : ℕ)

def piH_hom :
  (∏ (λ x : ℕ, (A.obj (op $ ι x)).homology n)) ⟶ (∏ (λ x : ℕ, (B.obj (op $ ι x)).homology n)) :=
pi.map $ λ k, (homology_functor _ _ _).map $ f.app _

def piδ (H : ∀ c n, short_exact ((f.app c).f n) ((g.app c).f n)) :
  (∏ (λ x : ℕ, (C.obj (op $ ι x)).homology n)) ⟶ (∏ (λ x : ℕ, (A.obj (op $ ι x)).homology (n+1))) :=
pi.map $ λ k, homological_complex.δ (f.app _) (g.app _) (H _) _ _ rfl

lemma piH_les (H : ∀ c n, short_exact ((f.app c).f n) ((g.app c).f n)) :
  exact_seq Ab.{u} [piH_hom f ι n, piH_hom g ι n, piδ f g ι n H, piH_hom f ι (n+1)] :=
begin
  apply exact.cons,
  { apply pi_map_exact, intro k,
    have := homological_complex.six_term_exact_seq _ _ (H (op $ ι k)) n (n+1) rfl,
    exact this.pair, },
  apply exact.cons,
  { apply pi_map_exact, intro k,
    have := homological_complex.six_term_exact_seq _ _ (H (op $ ι k)) n (n+1) rfl,
    exact (this.drop 1).pair, },
  apply exact.exact_seq,
  { apply pi_map_exact, intro k,
    have := homological_complex.six_term_exact_seq _ _ (H (op $ ι k)) n (n+1) rfl,
    exact (this.drop 2).pair, },
end

end step3

section step4

variables {A B C : system_of_complexes.{u}} (f : A.to_Ab ⟶ B.to_Ab) (g : B.to_Ab ⟶ C.to_Ab)
variables (n : ℕ) (ι : ℕ → ℝ≥0) (hι : monotone ι)

lemma shift_sub_id.bicartesian
  (HA₁ : is_iso (shift_sub_id (A.to_AbH n) ι hι))
  (HA₂ : is_iso (shift_sub_id (A.to_AbH (n+1)) ι hι))
  (H : ∀ c n, short_exact ((f.app c).f n) ((g.app c).f n)) :
  (@shift_sub_id.commsq (B.to_AbH n) (C.to_AbH n)
    (whisker_right g _) ι hι).bicartesian :=
begin
  rw ← commsq.bicartesian.symm_iff,
  let S : _ := _, show commsq.bicartesian S,
  have aux : _ := _,
  rw commsq.bicartesian_iff_isos _ _ aux aux S.kernel S S.cokernel,
  swap,
  { apply exact.cons, { exact exact_kernel_ι },
    apply exact.exact_seq, { exact abelian.exact_cokernel _ }, },
  clear aux,
  sorry
  -- use `HA₁` and `HA₂` and
  -- (important!) the fact that we have a `kernel.map` (resp. `cokernel.map`)
  -- arising between two identical exact sequences
end

end step4
