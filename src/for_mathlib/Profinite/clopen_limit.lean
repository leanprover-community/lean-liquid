import topology.category.Profinite.cofiltered_limit
import topology.discrete_quotient

import for_mathlib.order

noncomputable theory

open_locale classical

namespace Profinite

open category_theory
open category_theory.limits

universe u

variables {J : Type u} [semilattice_inf J] (F : J ⥤ Profinite.{u}) (C : cone F)

lemma image_eq (hC : is_limit C) (i : J) :
  set.range (C.π.app i) = ⋂ (j : J) (h : j ≤ i), set.range (F.map (hom_of_le h)) :=
begin
  refine le_antisymm _ _,
  { apply set.subset_Inter,
    intros j,
    apply set.subset_Inter,
    intros hj,
    rw ← C.w (hom_of_le hj),
    apply set.range_comp_subset_range },
  { rintro x hx,
    have cond : ∀ (j : J) (hj : j ≤ i), ∃ y : F.obj j, (F.map (hom_of_le hj)) y = x,
    { intros j hj,
      exact hx _ ⟨j,rfl⟩ _ ⟨hj, rfl⟩ },
    let Js := Σ' (a b : J), a ≤ b,
    let P := Π (j : J), F.obj j,
    let Us : Js → set P := λ e, { p | F.map (hom_of_le e.2.2) (p (e.1)) = p (e.2.1) ∧ p i = x},
    have hP : (_root_.is_compact (set.univ : set P)) := compact_univ,
    have hh := hP.inter_Inter_nonempty Us _ _,
    { rcases hh with ⟨z,hz⟩,
      let IC : (limit_cone F) ≅ C := (limit_cone_is_limit F).unique_up_to_iso hC,
      let ICX : (limit_cone F).X ≅ C.X := (cones.forget _).map_iso IC,
      let z : (limit_cone F).X := ⟨z,_⟩,
      swap,
      { intros a b h,
        convert (hz.2 _ ⟨⟨a, b, le_of_hom h⟩, rfl⟩).1 },
      use ICX.hom z,
      change (hC.lift _ ≫ _) _ = _,
      rw hC.fac,
      exact (hz.2 _ ⟨⟨i,i,le_refl _⟩,rfl⟩).2 },
    { intros i,
      refine is_closed.inter (is_closed_eq _ _) (is_closed_eq _ _);
      continuity },
    { have : ∀ e : J, nonempty (F.obj e),
      { intros e,
        rcases cond (e ⊓ i) inf_le_right with ⟨y,rfl⟩,
        use F.map (hom_of_le inf_le_left) y },
      haveI : ∀ j : J, inhabited (F.obj j) :=
        by {intros j, refine ⟨nonempty.some (this j)⟩},
      intros G,
      let GG := G.image (λ e : Js, e.1),
      haveI : inhabited J := ⟨i⟩,
      have := exists_le_finset (insert i GG),
      obtain ⟨j0,hj0⟩ := this,
      obtain ⟨x0,rfl⟩ := cond j0 (hj0 _ (finset.mem_insert_self _ _)),
      let z : P := λ e, if h : j0 ≤ e then F.map (hom_of_le h) x0 else (default _),
      use z,
      refine ⟨trivial, _⟩,
      rintros S ⟨e,rfl⟩,
      rintro T ⟨k,rfl⟩,
      dsimp [z],
      refine ⟨_, by erw dif_pos⟩,
      have : j0 ≤ e.fst,
      { apply hj0,
        apply finset.mem_insert_of_mem,
        rw finset.mem_image,
        refine ⟨e,k,rfl⟩ },
      erw [dif_pos this, dif_pos (le_trans this e.2.2)],
      change (F.map _ ≫ F.map _) _ = _,
      rw ← F.map_comp,
      refl } }
end

set_option pp.proofs true

lemma image_stabilizes [inhabited J] [∀ i, fintype (F.obj i)]
  (i : J) : ∃ (j : J) (hj : j ≤ i), ∀ (k : J) (hk : k ≤ j),
  set.range (F.map (hom_of_le $ le_trans hk hj)) =
  set.range (F.map (hom_of_le hj)) :=
begin
  have := eventually_constant i
    (λ e he, set.range (F.map (hom_of_le he))) _,
  swap,
  { intros a b ha hb h,
    dsimp,
    have : hom_of_le ha = (hom_of_le h) ≫ (hom_of_le hb) := rfl,
    rw [this, F.map_comp, Profinite.coe_comp],
    apply set.range_comp_subset_range },
  obtain ⟨j0,hj0,hh⟩ := this,
  use j0, use hj0,
  exact hh,
end

/-- The images of the transition maps stabilize, in which case they agree with
the image of the cone point. -/
theorem exists_image [inhabited J] [∀ i, fintype (F.obj i)]
  (hC : is_limit C) (i : J) : ∃ (j : J) (hj : j ≤ i),
  set.range (C.π.app i) = set.range (F.map $ hom_of_le $ hj) :=
begin
  have := Inter_eq i (λ e he, set.range (F.map (hom_of_le he))) _,
  swap,
  { intros a b ha hb hh,
    dsimp,
    have : hom_of_le ha = hom_of_le hh ≫ hom_of_le hb, refl,
    rw [this, F.map_comp, Profinite.coe_comp],
    apply set.range_comp_subset_range },
  obtain ⟨j0,hj0,hh⟩ := this,
  dsimp at hh,
  use j0, use hj0,
  rw [image_eq _ _ hC, ← hh],
end

end Profinite
