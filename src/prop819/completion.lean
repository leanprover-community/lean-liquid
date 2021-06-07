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
    1 (C.d _ _) _ _ ε hε f _,
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

lemma injective_of_strict_iso (F : strict_iso C D)
  (cond : ∀ (f : C.X 0) (hf : C.d 0 1 f = 0), f = 0) (f : D.X 0) (hf : D.d 0 1 f = 0) : f = 0 :=
begin
  let FF := (homological_complex.eval _ _ 0).map_iso F.iso,
  have : f = (FF.inv ≫ FF.hom) f, by {rw FF.inv_hom_id, simp},
  rw this,
  change FF.hom (FF.inv f) = 0,
  rw ←(show FF.hom 0 = 0, by simp),
  congr' 1,
  apply cond,
  change (F.iso.inv.f 0 ≫ C.d 0 1) f = 0,
  erw F.iso.inv.comm,
  change (F.iso.inv.f 1) _ = 0,
  erw hf,
  simp,
end

lemma exact_of_strict_iso (F : strict_iso C D) (ε : ℝ≥0) (hε : 0 < ε)
  (cond : ∀ (n : ℕ) (f : C.X (n+1)) (hf : C.d _ (n+2) f = 0), ∃ g : C.X n, C.d _ _ g = f ∧
  (nnnorm g) ≤ (1+ε) * nnnorm f) (n : ℕ) (f : D.X (n+1)) (hf : D.d _ (n+2) f = 0) :
  ∃ g : D.X n, D.d _ _ g = f ∧ nnnorm g ≤ (1 + ε) * nnnorm f :=
begin
  specialize cond n (((homological_complex.eval _ _ (n+1)).map_iso F.iso).inv f) _,
  { dsimp [homological_complex.eval],
    change (F.iso.inv.f (n+1) ≫ C.d (n+1) (n+2)) f = 0,
    rw F.iso.inv.comm,
    simp [hf] },
  rcases cond with ⟨g, h1, h2⟩,
  refine ⟨((homological_complex.eval _ _ n).map_iso F.iso).hom g, _, _⟩,
  { dsimp [homological_complex.eval] at *,
    change (F.iso.hom.f _ ≫ D.d _ _) _ = _,
    rw F.iso.hom.comm,
    simp [h1],
    let FF := (homological_complex.eval _ _ (n+1)).map_iso F.iso,
    change (FF.inv ≫ FF.hom) f = f,
    rw FF.inv_hom_id,
    refl },
  { rw SemiNormedGroup.strict_iso_inv at h2,
    rwa SemiNormedGroup.strict_iso_hom },
end
