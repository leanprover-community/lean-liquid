import topology.category.Profinite
import topology.discrete_quotient
import for_mathlib.topology

noncomputable theory

open_locale classical

namespace Profinite

open category_theory
open category_theory.limits

universe u

variables {J : Type u} [semilattice_inf J] (F : J ⥤ Profinite.{u}) (C : cone F)

-- We have the dual version of this in mathlib for directed preorders.
lemma exists_le_finset [inhabited J] (G : finset J) : ∃ j : J, ∀ g ∈ G, j ≤ g :=
begin
  apply G.induction_on,
  use (default J),
  tauto,
  rintros a S ha ⟨j0,h0⟩,
  use a ⊓ j0,
  intros g hg,
  rw finset.mem_insert at hg,
  cases hg,
  rw hg,
  exact inf_le_left,
  refine le_trans inf_le_right (h0 _ hg),
end

def created_cone : limits.cone F :=
  lift_limit (Top.limit_cone_is_limit $ F ⋙ Profinite_to_Top)

def created_cone_is_limit : limits.is_limit (created_cone F) :=
  lifted_limit_is_limit _

def cone_iso (hC : is_limit C) : C ≅ (created_cone F) :=
hC.unique_up_to_iso $ created_cone_is_limit _

def cone_point_iso (hC : is_limit C) : C.X ≅ (created_cone F).X :=
(cones.forget _).map_iso $ cone_iso _ _ hC

def created_iso : Profinite_to_Top.map_cone (created_cone F) ≅
  (Top.limit_cone $ F ⋙ Profinite_to_Top) :=
lifted_limit_maps_to_original _

def created_point_iso : Profinite_to_Top.obj (created_cone F).X ≅
  (Top.limit_cone $ F ⋙ Profinite_to_Top).X := (cones.forget _).map_iso $
created_iso _

def iso_to_Top (hC : is_limit C) : Profinite_to_Top.obj C.X ≅
  (Top.limit_cone $ F ⋙ Profinite_to_Top).X :=
  Profinite_to_Top.map_iso (cone_point_iso _ _ hC) ≪≫ created_point_iso _

def cone_homeo (hC : is_limit C) :
  C.X ≃ₜ (Top.limit_cone $ F ⋙ Profinite_to_Top).X :=
let FF := iso_to_Top _ _ hC in
{ to_fun := FF.hom,
  inv_fun := FF.inv,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp,
  continuous_to_fun := FF.hom.continuous,
  continuous_inv_fun := FF.inv.continuous }

def compact_space_of_limit (hC : is_limit C) :
  compact_space (Top.limit_cone $ F ⋙ Profinite_to_Top).X :=
begin
  constructor,
  rw ← homeomorph.compact_image (cone_homeo _ _ hC).symm,
  simp,
  exact compact_univ,
end

lemma product_topological_basis : topological_space.is_topological_basis
  { S : set (Π (j : J), F.obj j) |
    ∃ (Us : Π (j : J), set (F.obj j)) (F : finset J),
      (∀ j, j ∈ F → is_open (Us j)) ∧ S = (F : set J).pi Us } :=
topological_basis_pi _

-- TODO: Golfing required!
-- TODO: This generalizes to any cofiltered limit in Top -- Generalize before moving to mathlib!
lemma limit_topological_basis [inhabited J] : topological_space.is_topological_basis
  { S : set (Top.limit_cone $ F ⋙ Profinite_to_Top).X |
    ∃ (j : J) (U : set (F.obj j)) (hU : is_open U),
      S = (Top.limit_cone $ F ⋙ Profinite_to_Top).π.app j ⁻¹' U } :=
begin
  let ι : (Top.limit_cone $ F ⋙ Profinite_to_Top).X → Π (j : J), F.obj j :=
    λ x, x.val,
  convert pullback_topological_basis ι ⟨rfl⟩ _ (product_topological_basis F),
  funext S,
  ext,
  split,
  { intro h,
    obtain ⟨j,U,hU,rfl⟩ := h,
    let Us : Π (j : J), set (F.obj j) := λ k, if h : k = j then by {rw h, exact U} else set.univ,
    let FF : finset J := {j},
    use (FF : set J).pi Us, use Us, use FF,
    split,
    { intros k hk,
      dsimp [FF] at hk,
      simp at hk,
      rw hk,
      dsimp [Us],
      rw if_pos rfl,
      exact hU },
    { refl },
    { dsimp [set.pi],
      ext,
      split,
      { intros hx k hk,
        dsimp [FF] at hk,
        simp at hk,
        subst hk,
        dsimp [Us],
        rwa if_pos rfl },
      { intro hx,
        specialize hx j _,
        dsimp [FF],
        simp,
        dsimp [Us] at hx,
        rwa if_pos rfl at hx } } },
  { intro h,
    obtain ⟨B,hB,rfl⟩ := h,
    obtain ⟨Us,FF,h1,rfl⟩ := hB,
    obtain ⟨j0,hj0⟩ := exists_le_finset FF,
    use j0,
    let U : set (F.obj j0) :=
      ⋂ (j : J) (hj : j ∈ FF), (F.map (hom_of_le (hj0 j hj))) ⁻¹' (Us j),
    use U,
    split,
    { let Vs : J → set (F.obj j0) :=
        λ j, if hj : j ∈ FF then ⇑(F.map (hom_of_le (hj0 j hj))) ⁻¹' (Us j) else set.univ,
      have := @is_open_bInter _ J _ FF Vs FF.finite_to_set _,
      swap,
      { intros i hi,
        dsimp [Vs],
        rw dif_pos,
        swap, { exact hi },
        apply is_open.preimage,
        continuity,
        exact h1 _ hi },
      convert this,
      dsimp [U, Vs],
      apply set.Inter_congr (λ j : J, j) (by tauto),
      intros j,
      congr' 1,
      funext hj,
      dsimp at hj ⊢,
      rw dif_pos hj },
    { dsimp [U, set.pi],
      simp_rw set.preimage_Inter,
      ext,
      have useful1 : ∀ (a b : J) (h : a ≤ b), ⇑(F.map (hom_of_le h)) =
          ⇑((F ⋙ Profinite_to_Top).map (hom_of_le h)),
        { intros _ _ _, refl },
      have useful2 : ∀ (a b c : Top) (f : a ⟶ b) (g : b ⟶ c) (x : a), (f ≫ g) x =
          g (f x) := by tauto,
      split,
      { intro hx,
        dsimp at hx,
        rintros i ⟨i,rfl⟩,
        dsimp,
        rintros _ hi,
        cases hi with hi hh,
        dsimp at hh,
        rw ← hh,
        change _ ∈ Us i,
        erw useful1,
        rw ← useful2,
        let C := Top.limit_cone (F ⋙ Profinite_to_Top),
        rw C.w,
        apply hx,
        exact hi },
      { intros hx,
        intros i hi,
        specialize hx _ ⟨i,rfl⟩ _ ⟨hi, rfl⟩,
        dsimp at hx,
        erw useful1 at hx,
        change _ ∈ Us i at hx,
        rw ← useful2 at hx,
        rwa (Top.limit_cone (F ⋙ Profinite_to_Top)).w at hx } } }
end

lemma exists_clopen' [inhabited J] (hC : is_limit C)
  (U : set (Top.limit_cone $ F ⋙ Profinite_to_Top).X) (hU : is_clopen U) :
  ∃ (j : J) (V : set (F.obj j)) (hV : is_clopen V),
  U = ((Top.limit_cone $ F ⋙ Profinite_to_Top).π.app j) ⁻¹' V :=
begin
  let CC := (Top.limit_cone (F ⋙ Profinite_to_Top)),
  let XX := CC.X,
  haveI := compact_space_of_limit _ _ hC,
  cases hU with hUOpen hUClosed,
  have hUCompact := hUClosed.is_compact,
  obtain ⟨S,hS,hh⟩ := (limit_topological_basis F).open_eq_sUnion hUOpen,
  let js : S → J := λ a, classical.some (hS a.2),
  let Us : Π (s : S), set (F.obj (js s)) := λ a,
    classical.some (classical.some_spec (hS a.2)),
  have hUsOpen : ∀ (s : S), is_open (Us s),
  { intros s,
    have := classical.some_spec (classical.some_spec (hS s.2)),
    cases this with h1 _,
    exact h1 },
  have hUseq : ∀ (s : S), (s : set XX) = CC.π.app (js s) ⁻¹' (Us s),
  { intros s,
    have := classical.some_spec (classical.some_spec (hS s.2)),
    cases this with _ h1,
    exact h1 },
  have hClopens : ∀ (s : S), ∃ (T : set (set (F.obj (js s))))
    (hT : T ⊆ { A : set (F.obj (js s)) | is_clopen A}), (Us s) = ⋃₀T,
  { intros s,
    exact is_topological_basis_clopen.open_eq_sUnion (hUsOpen s) },
  let Ts : Π (s : S), set (set (F.obj (js s))) := λ s,
    classical.some (hClopens s),
  have hTs : ∀ (s : S) (t : Ts s), is_clopen (t : set (F.obj (js s))),
  { intros s t,
    have := classical.some_spec (hClopens s),
    cases this with hh1 hh2,
    apply hh1,
    exact t.2 },
  have hTsCover : ∀ (s : S), Us s = ⋃ (t : Ts s), (t : set (F.obj (js s))),
  { intros s,
    have := classical.some_spec (hClopens s),
    cases this with hh1 hh2,
    rw hh2,
    ext u, split,
    { intro hu,
      rcases hu with ⟨A,hA,hu⟩,
      refine ⟨A,⟨⟨A,hA⟩,rfl⟩,hu⟩ },
    { intro hu,
      rcases hu with ⟨A,⟨⟨A,hA⟩,rfl⟩,hu⟩,
      exact ⟨A,hA,hu⟩ } },
  let ST := Σ (s : S), Ts s,
  let Bs : ST → set XX :=
    λ e, (CC.π.app (js e.1)) ⁻¹' (e.2 : set (F.obj (js e.1))),
  have := hUCompact.elim_finite_subcover Bs _ _,
  { obtain ⟨FF,hFF⟩ := this,
    let js' : ST → J := λ e, js e.1,
    let GG : finset J := FF.image js',
    obtain ⟨j0,hj0⟩ := exists_le_finset GG,
    have hGG : ∀ (e : ST) (he : e ∈ FF), j0 ≤ js' e,
    { intros e he,
      suffices : js' e ∈ GG,
      { apply hj0 _ this },
      dsimp [GG],
      rw finset.mem_image,
      refine ⟨e,he,rfl⟩ },
    use j0,
    let Vs : Π (e : ST) (he : e ∈ FF), set (F.obj j0) := λ e he,
      F.map (hom_of_le (hGG _ he)) ⁻¹' (e.2 : set (F.obj (js e.1))),
    let V : set (F.obj j0) := ⋃ (e : ST) (he : e ∈ FF), Vs e he,
    use V,
     have useful1 : ∀ (a b : J) (h : a ≤ b), ⇑(F.map (hom_of_le h)) =
      ⇑((F ⋙ Profinite_to_Top).map (hom_of_le h)),
      { intros _ _ _, refl },
    have useful2 : ∀ (a b c : Top) (f : a ⟶ b) (g : b ⟶ c) (x : a), (f ≫ g) x =
      g (f x) := by tauto,
    have useful3 : ∀ (a b c : Top) (f : a ⟶ b) (g : b ⟶ c),
      (f ≫ g : a → c) = g ∘ f := by { intros _ _ _ _ _, refl },
    split,
    { split,
      { apply is_open_Union,
        intros e,
        apply is_open_Union,
        intros he,
        dsimp [Vs],
        apply is_open.preimage,
        continuity,
        refine (hTs _ _).1 },
      { dsimp [V, Vs],
        apply is_closed_bUnion',
        intros e he,
        apply is_closed.preimage,
        continuity,
        refine (hTs _ _).2 } },
    { -- use hh, hFF and hTsCover
      dsimp [V],
      rw set.preimage_Union,
      ext w,
      split,
      { intro hw,
        replace hw := hFF hw,
        rcases hw with ⟨e,⟨e,rfl⟩,hw1,⟨hw,rfl⟩,hw2⟩,
        dsimp at hw2,
        use Bs e,
        refine ⟨⟨e,_⟩, hw2⟩,
        dsimp,
        rw set.preimage_Union,
        dsimp [Bs],
        simp [hw],
        rw [useful1, ← set.preimage_comp, ← useful3, CC.w] },
      { intro hw,
        rcases hw with ⟨A,⟨e,rfl⟩,hw⟩,
        dsimp at hw,
        rw set.preimage_Union at hw,
        rcases hw with ⟨he1,⟨he,rfl⟩,hw⟩,
        dsimp at hw,
        rw hh,
        use e.1,
        split, { exact e.1.2 },
        erw hUseq,
        change _ ∈ Us e.1,
        rw hTsCover,
        use e.2,
        split,
        { use e.2 },
        { rwa [useful1, ← set.preimage_comp, ← useful3, CC.w] at hw } } } },
  { -- use hTs,
    intros e,
    dsimp [Bs],
    apply is_open.preimage,
    continuity,
    refine (hTs _ _).1 },
  { -- use hh,
    intros x hx,
    rw hh at hx,
    rcases hx with ⟨A,hA,hx⟩,
    let s : S := ⟨A,hA⟩,
    change x ∈ (s : set XX) at hx,
    rw hUseq at hx,
    rw hTsCover at hx,
    rw set.preimage_Union at hx,
    rcases hx with ⟨HH,⟨tt,htt⟩,hhx⟩,
    dsimp at htt,
    dsimp [Bs],
    refine ⟨HH,_,hhx⟩,
    use ⟨s,tt⟩,
    dsimp,
    exact htt }
end

/-- The existence of a clopen. -/
theorem exists_clopen [inhabited J]
  (hC : is_limit C) (U : set C.X) (hU : is_clopen U) :
  ∃ (j : J) (V : set (F.obj j)) (hV : is_clopen V), U = (C.π.app j) ⁻¹' V :=
begin
  let FF := cone_homeo _ _ hC,
  let UU := FF.symm ⁻¹' U,
  have hUU : is_clopen UU,
  { split,
    exact is_open.preimage (FF.symm.continuous) hU.1,
    exact is_closed.preimage (FF.symm.continuous) hU.2 },
  rcases exists_clopen' F _ hC UU hUU with ⟨j,V,hV,hJ⟩,
  use j, use V, use hV,
  dsimp only [UU] at hJ,
  have : U = FF ⁻¹' (((Top.limit_cone (F ⋙ Profinite_to_Top)).π.app j) ⁻¹' V),
  { rw [← hJ, ← set.preimage_comp],
    simp },
  rw this,
  rw ← set.preimage_comp,
  congr' 1,
  have : C.π.app j = (cone_point_iso _ _ hC).hom ≫ (created_cone _).π.app j,
  { have := (cone_iso _ _ hC).hom.w,
    rw ← this,
    refl },
  rw this,
  refl,
end

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
    haveI : compact_space P := by apply_instance,
    have hP : (_root_.is_compact (set.univ : set P)) := compact_univ,
    have hh := hP.inter_Inter_nonempty Us _ _,
    { rcases hh with ⟨z,hz⟩,
      let IC : (limit_cone F) ≅ C := (limit_cone_is_limit F).unique_up_to_iso hC,
      let ICX : (limit_cone F).X ≅ C.X := (cones.forget _).map_iso IC,
      let z : (limit_cone F).X := ⟨z,_⟩,
      swap,
      { dsimp,
        intros a b h,
        let e : Js := ⟨a,b,le_of_hom h⟩,
        cases hz with _ hz,
        specialize hz _ ⟨e,rfl⟩,
        dsimp at hz,
        cases hz with hz _,
        convert hz },
      use ICX.hom z,
      dsimp,
      change (hC.lift _ ≫ _) _ = _,
      rw hC.fac,
      cases hz with _ hz,
      specialize hz _ ⟨⟨i,i,le_refl _⟩,rfl⟩,
      exact hz.2 },
    { intros i,
      apply is_closed.inter,
      apply is_closed_eq,
      continuity,
      apply is_closed_eq,
      continuity },
    { have : ∀ e : J, nonempty (F.obj e),
      { intros e,
        let ee := e ⊓ i,
        specialize cond ee inf_le_right,
        rcases cond with ⟨y,rfl⟩,
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
      dsimp,
      rintro T ⟨k,rfl⟩,
      dsimp,
      split,
      { dsimp [z],
        have : j0 ≤ e.fst,
        { apply hj0,
          rw finset.mem_insert,
          right,
          dsimp [GG],
          rw finset.mem_image,
          use e,
          refine ⟨k,rfl⟩ },
        erw dif_pos this,
        erw dif_pos (le_trans this e.2.2),
        change (F.map _ ≫ F.map _) _ = _,
        rw ← F.map_comp,
        refl },
      { dsimp [z],
        erw dif_pos } } }
end

/- Not sure about the best formulation...
/-- The images of the transition maps stabilize. -/
lemma image_stabilizes [∀ i, fintype (F.obj i)]
  (i : J) : ∃ (j : J) (hj : j ≤ i), ∀ (k : J) (hk : k ≤ j),
  set.range (F.map (hom_of_le hj)) =
  set.range (F.map (hom_of_le $ le_trans hk hj)) := sorry

/-- The images of the transition maps stabilize, in which case they agree with
the image of the cone point. -/
theorem exists_image [∀ i, fintype (F.obj i)]
  [∀ i, discrete_topology (F.obj i)] (hC : is_limit C) (i : J) :
  ∃ (j : J) (hj : j ≤ i),
  set.range (C.π.app i) = set.range (F.map $ hom_of_le $ hj) :=
begin
  obtain ⟨j,hj,h⟩ := image_stabilizes F i,
  use j, use hj,
  refine le_antisymm _ _,
  { rw ← C.w (hom_of_le hj),
    rw Profinite.coe_comp,
    apply set.range_comp_subset_range },
  { rw image_eq _ _ hC,
    sorry,
  },
end
-/

/-- Any discrete quotient arises from some point in the limit. -/
theorem exists_discrete_quotient [∀ i, fintype (F.obj i)] (hC : is_limit C)
  (S : discrete_quotient C.X) : ∃ (i : J) (T : discrete_quotient (F.obj i)),
  S = T.comap (C.π.app i).continuous := sorry

end Profinite
