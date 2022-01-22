import condensed.extr.basic
import condensed.proetale_site
import condensed.basic
import category_theory.sites.induced_topology

import for_mathlib.presieve

open category_theory

universes u v' u'

def ExtrDisc.cover_dense :
  cover_dense proetale_topology.{u} ExtrDisc_to_Profinite.{u} :=
  cover_dense.mk $ λ U,
begin
  change ∃ R, _,
  obtain ⟨⟨T,hT,π,hπ⟩⟩ := enough_projectives.presentation U,
  dsimp at hT hπ,
  let R : presieve U := presieve.of_arrows (λ i : punit, T) (λ i, π),
  use R,
  split,
  { refine ⟨punit, infer_instance, λ i, T, λ i, π, λ x, ⟨punit.star, _⟩, rfl⟩,
    rw Profinite.epi_iff_surjective at hπ,
    exact hπ x },
  intros Y f hf,
  change nonempty _,
  rcases hf with ⟨a,b⟩,
  let t : presieve.cover_by_image_structure ExtrDisc_to_Profinite π := _,
  swap,
  { resetI,
    refine ⟨⟨T⟩, 𝟙 _, π, by simp⟩ },
  use t,
end

def ExtrDisc.proetale_topology : grothendieck_topology ExtrDisc.{u} :=
  ExtrDisc.cover_dense.induced_topology.{u}

@[derive category]
def ExtrSheaf (C : Type u') [category.{v'} C] := Sheaf ExtrDisc.proetale_topology.{u} C

-- TODO: cover_densed.Sheaf_equiv still has unecessary universe restrictions that can be relaxed.
noncomputable
def Condensed_ExtrSheaf_equiv (C : Type u') [category.{u+1} C] [limits.has_limits C] :
  ExtrSheaf.{u} C ≌ Condensed.{u} C :=
ExtrDisc.cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting
  ExtrDisc.cover_dense.locally_cover_dense.induced_topology_cover_preserving
  ExtrDisc.cover_dense.locally_cover_dense.induced_topology_cover_lifting

-- Sanity check
@[simp] lemma Condensed_ExtrSheaf_equiv_inverse_val (C : Type u') [category.{u+1} C]
  [limits.has_limits C] (F : Condensed.{u} C) :
  ((Condensed_ExtrSheaf_equiv C).inverse.obj F).val = ExtrDisc_to_Profinite.op ⋙ F.val := rfl

open opposite

def is_ExtrSheaf_of_types (P : ExtrDisc.{u}ᵒᵖ ⥤ Type u') : Prop :=
∀ (B : ExtrDisc.{u}) (ι : Type u) [fintype ι] (α : ι → ExtrDisc.{u})
  (f : Π i, α i ⟶ B) (hf : ∀ b : B, ∃ i (x : α i), f i x = b)
  (x : Π i, P.obj (op (α i)))
  (hx : ∀ (i j : ι) (Z : ExtrDisc) (g₁ : Z ⟶ α i) (g₂ : Z ⟶ α j),
    g₁ ≫ f _ = g₂ ≫ f _ → P.map g₁.op (x _) = P.map g₂.op (x _)),
∃! t : P.obj (op B), ∀ i, P.map (f i).op t = x _

theorem is_ExtrSheaf_of_types_of_is_sheaf_ExtrDisc_proetale_topology
  (F : ExtrDiscᵒᵖ ⥤ Type u') (H : presieve.is_sheaf ExtrDisc.proetale_topology F) :
  is_ExtrSheaf_of_types F :=
begin
  introsI B ι _ X f hf x hx,
  let S : presieve B := presieve.of_arrows X f,
  specialize H (sieve.generate S) _,
  { dsimp [ExtrDisc.proetale_topology],
    let R : presieve B.val := presieve.of_arrows (λ i, (X i).val) (λ i, (f i).val),
    use R,
    split,
    { use [ι, infer_instance, (λ i, (X i).val), (λ i, (f i).val), hf, rfl] },
    { intros Y f hf,
      rcases hf with ⟨i⟩,
      use [X i, f i, 𝟙 _],
      refine ⟨_, by simp⟩,
      use [X i, 𝟙 _, (f i), presieve.of_arrows.mk i],
      simp } },
  rw ← presieve.is_sheaf_for_iff_generate at H,
  let t : S.family_of_elements F := presieve.mk_family_of_elements_of_arrows X f F x,
  have ht : t.compatible := presieve.mk_family_of_elements_of_arrows_compatible X f F x hx,
  specialize H t ht,
  -- now use H.
  obtain ⟨tt,htt,htt'⟩ := H,
  refine ⟨tt,_,_⟩,
  { dsimp,
    intros i,
    specialize htt (f i) (presieve.of_arrows.mk i),
    rw htt,
    apply presieve.mk_family_of_elements_of_arrows_eval _ _ _ _ hx },
  { intros y hy,
    apply htt',
    intros Z f hf,
    rcases hf with ⟨i⟩,
    rw hy,
    symmetry,
    apply presieve.mk_family_of_elements_of_arrows_eval _ _ _ _ hx }
end

-- This is more or less proved in the profinite case, along with a condition
-- that equalizers should be compatible, while the equalizer condition in the
-- ExtrDisc case can be found (in some form) in `condensed/extr.lean`.
-- It will take some time to convert these proofs to this case, but this is
-- very doable!
theorem ExtrSheaf_iff_is_ExtrSheaf_of_types
  (F : ExtrDiscᵒᵖ ⥤ Type u') (H : is_ExtrSheaf_of_types F) :
  presieve.is_sheaf ExtrDisc.proetale_topology F :=
begin
  sorry
  /-
  intros B S hS,
  change proetale_topology _ _ at hS,
  rw ExtrDisc.cover_dense.locally_cover_dense.pushforward_cover_iff_cover_pullback at hS,
  obtain ⟨⟨T,hT⟩,rfl⟩ := hS,
  obtain ⟨R,hR,hRT⟩ := hT,
  dsimp,
  let R' := presieve.functor_pullback ExtrDisc_to_Profinite R,
  have : R' ≤ sieve.functor_pullback ExtrDisc_to_Profinite T,
  { sorry },
  have h : sieve.generate R' ≤ sieve.functor_pullback ExtrDisc_to_Profinite T,
  { sorry },
  apply category_theory.presieve.is_sheaf_for_subsieve,
  rotate 2,
  exact sieve.generate R',
  exact h,
  intros Y f,
  let R'' : presieve Y := sorry,
  have : sieve.pullback f (sieve.generate R') =
    sieve.generate R'' := sorry,
  intros x hx,
  dsimp [R'] at x,
  obtain ⟨ι,_,X,π,surj,rfl⟩ := hR,
  resetI,
  -- Now choose a projective presentation of (P i) for all i, and project onto the first object.
  -- This gives a cover of Y, which we can plug in to H.
  let PP : ι → ExtrDisc := λ i, (Profinite.pullback f.val (π i)).pres,
  let pp : Π i, PP i ⟶ Y := λ i,
    ⟨(Profinite.pullback f.val (π i)).pres_π ≫ Profinite.pullback.fst _ _⟩,
  let y : Π i, F.obj (op (PP i)) := λ i, x (pp i) sorry,

  specialize H Y ι PP pp sorry y sorry,

  obtain ⟨t,h1,h2⟩ := H,
  refine ⟨t,_,_⟩,
  { dsimp,
    intros W g hg,
    change ∃ Q, _ at hg,
    obtain ⟨Q,q,r,hr,hq⟩ := hg,
    change (presieve.of_arrows _ _) _ at hr,
    rw presieve.mem_of_arrows_iff at hr,
    obtain ⟨i,e,hh⟩ := hr,
    dsimp [y] at h1,
    specialize h1 i,
    specialize hx q g,

  },
  { intros a ha,
    apply h2,
    intros i,
    apply ha }
  -/
end
