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
  intros B S hS x hx,
  obtain ⟨R,hR,hRS⟩ := hS,
  obtain ⟨ι,hh,X,f,surj,rfl⟩ := hR,
  resetI,
  dsimp [sieve.functor_pushforward, presieve.functor_pushforward] at hRS,
  have : ∀ i : ι, ∃ (G : ExtrDisc) (π : G ⟶ B)
    (g : X i ⟶ G.val) (hπ : S π), (f i) = g ≫ π.val,
  { intros i,
    specialize hRS (X i) (presieve.of_arrows.mk i),
    obtain ⟨G,π,g,hπ,hhh⟩ := hRS,
    use [G,π,g,hπ,hhh] },
  choose G π g hπ hhh using this,
  specialize H B ι G π _,
  { sorry },
  let y : Π (i : ι), F.obj (op (G i)) := λ i, x (π i) (hπ _),
  specialize H y _,
  { intros i j W e₁ e₂,
    apply hx },
  obtain ⟨t,ht1,ht2⟩ := H,
  refine ⟨t,_,_⟩,
  { intros Z f hf,
    sorry },
  { intros z hz,
    apply ht2,
    intros i,
    apply hz }

end
