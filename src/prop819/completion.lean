import for_mathlib.SemiNormedGroup
import algebra.homology.additive
import locally_constant.Vhat
import normed_group.controlled_exactness
import prop819.strict_complex_iso

noncomputable theory

universes u

variables (C D : cochain_complex SemiNormedGroup.{u} ℕ)

open SemiNormedGroup

/-- The completed cochain complex associated to C. -/
abbreviation cmpl := (Completion.map_homological_complex _).obj C

open_locale nnreal

lemma cmpl_exact_of_exact (ε : ℝ≥0) (hε : 0 < ε)
  (cond : ∀ (n : ℕ) (f : C.X (n+1)) (hf : C.d (n+1) (n+2) f = 0),
    ∃ g : C.X n, C.d _ _ g = f ∧ (nnnorm g) ≤ (nnnorm f)) (n : ℕ) (f : (cmpl C).X (n+1))
    (hf : (cmpl C).d _ (n+2) f = 0) : ∃ g : (cmpl C).X n, (cmpl C).d _ _ g = f ∧
    (nnnorm g) ≤ (1 + ε) * (nnnorm f) :=
begin
  have := @controlled_exactness (C.X (n+1)) (C.X n) (C.X (n+2)) _ _ _ (C.d _ _) 1 zero_lt_one
    1 (C.d _ _) _ _ f _ ε hε,
  { rcases this with ⟨g,hg1,hg2⟩,
    exact ⟨g,hg1,hg2⟩ },
  { intros g hg,
    erw add_monoid_hom.mem_ker at hg,
    specialize cond _ g hg,
    rcases cond with ⟨g',h1,h2⟩,
    refine ⟨g',h1,_⟩,
    simpa },
  { rintros g ⟨g,rfl⟩,
    specialize cond (n+1) (C.d (n+1) (n+2) g) _,
    { change (C.d (n+1) (n+2) ≫ C.d (n+2) (n+3)) g = 0,
      simp },
    rcases cond with ⟨g',h1,h2⟩,
    refine ⟨g',h1,_⟩,
    dsimp,
    simp,
    exact h2 },
  { erw add_monoid_hom.mem_ker,
    exact hf },
end

lemma exact_of_strict_iso (F : strict_iso C D) (ε : ℝ≥0) (hε : 0 < ε)
  (cond : ∀ (n : ℕ) (f : C.X (n+1)) (hf : C.d _ (n+2) f = 0), ∃ g : C.X n, C.d _ _ g = f ∧
  (nnnorm g) ≤ (1+ε) * nnnorm f) (n : ℕ) (f : D.X (n+1)) (hf : D.d _ (n+2) f = 0) :
  ∃ g : D.X n, D.d _ _ g = f ∧ nnnorm g ≤ (1 + ε) * nnnorm f :=
begin
  specialize cond n (((homological_complex.eval_at (n+1)).map_iso F.iso).inv f) _,
  { dsimp [homological_complex.eval_at],
    change (F.iso.inv.f (n+1) ≫ C.d (n+1) (n+2)) f = 0,
    rw F.iso.inv.comm,
    simp [hf] },
  rcases cond with ⟨g, h1, h2⟩,
  refine ⟨((homological_complex.eval_at n).map_iso F.iso).hom g, _, _⟩,
  { dsimp [homological_complex.eval_at] at *,
    change (F.iso.hom.f _ ≫ D.d _ _) _ = _,
    rw F.iso.hom.comm,
    simp [h1],
    let FF := (homological_complex.eval_at (n+1)).map_iso F.iso,
    change (FF.inv ≫ FF.hom) f = f,
    rw FF.inv_hom_id,
    refl },
  { rw SemiNormedGroup.strict_iso_inv at h2,
    rwa SemiNormedGroup.strict_iso_hom },
end
