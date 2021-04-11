--import .PartialOrder
import .Profinite
import topology.category.Profinite
import topology.locally_constant.basic
import category_theory.Fintype
import category_theory.limits.creates
import category_theory.arrow
import order.category.PartialOrder

/-!
This file proves that a profinite set is a limit of finite sets.
Some portions of this file were inspired by code in the `Profinite2` branch of mathlib,
due to C. Sönne and B. Mehta.
-/

universe u
open category_theory

noncomputable theory

namespace Profinite

section move_me

-- TODO: Move this and clean up proofs above
@[simp]
lemma comp_apply {X Y Z : Profinite.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) := rfl

-- TODO: Move this and clean up proofs above
@[simp]
lemma id_apply {X : Profinite.{u}} (x : X) : (𝟙 X : X ⟶ X) x = x := rfl

@[simp]
lemma id_to_fun {X : Profinite.{u}} : (𝟙 X : X → X) = id := rfl

-- TODO: Move this!
@[simp]
lemma comp_to_fun {X Y Z : Profinite.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g : X → Z) = g ∘ f := rfl

end move_me

variables (X : Profinite.{u})

@[ext]
structure cl :=
(sets : set (set X))
(clopen : ∀ S : sets, is_clopen (S : set X))
(nonempty : ∀ S : sets, (S : set X).nonempty)
(cover : ∀ x : X, ∃! U: sets, x ∈ (U : set X))

variable {X}

namespace cl

def of_clopen {U : set X} : is_clopen U → U.nonempty → Uᶜ.nonempty → X.cl := λ h1 h2 h3,
{ sets := {U,Uᶜ},
  clopen := begin
    rintro ⟨V,rfl|h⟩, { assumption },
    rw set.mem_singleton_iff at h,
    simp [h, is_clopen_compl h1],
  end,
  nonempty := begin
    rintro ⟨V,rfl|h⟩, { assumption },
    rw set.mem_singleton_iff at h,
    simpa [h],
  end ,
  cover := begin
    rintro x,
    by_cases hx : x ∈ U,
    { refine ⟨⟨U,or.inl rfl⟩, hx, _⟩,
      rintros ⟨V,rfl|hV⟩ hhV, { refl },
      rw set.mem_singleton_iff at hV,
      ext1,
      dsimp at hhV,
      rw hV at hhV,
      exact false.elim (hhV hx) },
    { refine ⟨⟨Uᶜ, or.inr rfl⟩, hx, _⟩,
      rintros ⟨V,rfl|hV⟩ hhV,
      { exact false.elim (hx hhV) },
      { simpa using hV } }
  end }

instance : has_coe_to_sort X.cl := ⟨Type*, λ I, I.sets⟩

def of_clopen.mk {U : set X} {h1 : is_clopen U} {h2 : U.nonempty} {h3 : Uᶜ.nonempty} :
  of_clopen h1 h2 h3 := ⟨U, or.inl rfl⟩

lemma is_open {I : X.cl} (U : I) : is_open (U : set X) :=
  (I.clopen _).1

lemma is_closed {I : X.cl} (U : I) : is_closed (U : set X) :=
  (I.clopen _).2

instance {I : X.cl} : fintype I :=
begin
  have h : _root_.is_compact (⊤ : set X) := compact_univ,
  rw compact_iff_finite_subcover at h,
  specialize h (λ i : I, i) (λ i, is_open _) (λ x _, _),
  rcases I.cover x with ⟨U,hU,hU2⟩,
  refine ⟨U,⟨U,rfl⟩,hU⟩,
  let S := classical.some h,
  let hS := classical.some_spec h,
  refine ⟨S,_⟩,
  intros U,
  rcases I.nonempty U with ⟨x,hx⟩,
  specialize hS (by tauto : x ∈ _),
  rcases hS with ⟨V,⟨W,rfl⟩,W,⟨(h1 : _ ∈ S),rfl⟩,h2⟩,
  dsimp at h2,
  suffices : U = W, by rwa this,
  rcases I.cover x with ⟨S,hS,hh⟩,
  rw [hh U hx, hh W h2],
end

instance : inhabited X.cl :=
begin
  by_cases h : _root_.nonempty X,
  { refine ⟨⟨{set.univ}, by simp, _, by tidy⟩⟩,
    rcases h with ⟨x⟩,
    rintro ⟨h,hh⟩,
    refine ⟨x,_⟩,
    simp only [set.mem_singleton_iff] at hh,
    simp [hh] },
  { refine ⟨⟨∅, by simp, by simp, λ x, false.elim (h ⟨x⟩)⟩⟩ }
end

lemma eq_of_le {I : X.cl} (U V : I) : (U : set X) ≤ V → U = V :=
begin
  intro h,
  rcases (I.nonempty U) with ⟨y,hy⟩,
  rcases I.cover y with ⟨W,h1,h2⟩,
  rw [h2 U hy, h2 V (h hy)],
end

-- Discrete topology
instance {I : X.cl} : topological_space I := ⊥

-- I ≤ J iff I refines J
instance : preorder X.cl :=
{ le := λ I J, ∀ U : I, ∃ V : J, (U : set X) ≤ V,
  le_refl := λ I U, ⟨U, le_refl _⟩,
  le_trans := λ I J K h1 h2 U,
    let ⟨V,hV⟩ := h1 U,
        ⟨W,hW⟩ := h2 V
    in ⟨W, le_trans hV hW⟩ }

def common (I J : X.cl) : X.cl :=
{ sets := { U | (U : set X).nonempty ∧ ∃ (A : I) (B : J), (U : set X) = A ⊓ B },
  clopen := begin
    rintro ⟨U,hU1,⟨A,B,rfl⟩⟩,
    exact is_clopen_inter (clopen _ _) (clopen _ _),
  end,
  nonempty := λ U, U.2.1,
  cover := begin
    intro x,
    rcases I.cover x with ⟨A,hA1,hA2⟩,
    rcases J.cover x with ⟨B,hB1,hB2⟩,
    refine ⟨⟨(A ⊓ B : set X),⟨x,hA1,hB1⟩,⟨A,B,rfl⟩⟩,⟨hA1,hB1⟩,_⟩,
    rintros ⟨W,⟨W,A',B',rfl⟩⟩ hW2,
    have : A' = A,
    { apply hA2,
      exact hW2.1 },
    subst this,
    have : B' = B,
    { apply hB2,
      exact hW2.2 },
    subst this,
  end }

lemma common_le_left {I J : X.cl} : common I J ≤ I :=
begin
  rintro ⟨U, ⟨U, A, B, rfl⟩⟩,
  refine ⟨A, set.inter_subset_left _ _⟩,
end

lemma common_le_right {I J : X.cl} : common I J ≤ J :=
begin
  rintro ⟨U, ⟨U, A, B, rfl⟩⟩,
  refine ⟨B, set.inter_subset_right _ _⟩,
end


instance : semilattice_inf X.cl :=
{ inf := common,
  le_antisymm := begin
    intros I J h1 h2,
    ext S,
    split,
    { intro hS,
      rcases h1 ⟨S,hS⟩ with ⟨V,hV⟩,
      have : S = V,
      { apply le_antisymm hV,
        rcases h2 V with ⟨W,hW⟩,
        have : W = ⟨S,hS⟩,
        { symmetry,
          apply eq_of_le,
          refine le_trans hV hW },
        rwa ← this },
      rw this,
      exact V.2 },
    { intro hS,
      rcases h2 ⟨S,hS⟩ with ⟨V,hV⟩,
      have : S = V,
      { apply le_antisymm hV,
        rcases h1 V with ⟨W,hW⟩,
        have : W = ⟨S,hS⟩,
        { symmetry,
          apply eq_of_le,
          refine le_trans hV hW },
        rwa ← this },
      rw this,
      exact V.2 }
  end,
  inf_le_left := λ _ _, common_le_left,
  inf_le_right := λ _ _, common_le_right,
  le_inf := begin
    intros I J K h1 h2 U,
    rcases h1 U with ⟨A,hA⟩,
    rcases h2 U with ⟨B,hB⟩,
    have : (U : set X) ≤ A ⊓ B := le_inf hA hB,
    refine ⟨⟨A ⊓ B,set.nonempty.mono this (I.nonempty U),A,B,rfl⟩, this⟩,
  end,
  ..(infer_instance : preorder _)}

lemma inf_mono_right {I : X.cl} : monotone (λ J : X.cl, I ⊓ J) :=
begin
  intros J K h,
  rintro ⟨U,⟨hU,V,W,rfl⟩⟩,
  rcases h W with ⟨R,hR⟩,
  have : (V : set X) ⊓ W ≤ V ⊓ R := λ x ⟨h1,hx⟩, ⟨h1,hR hx⟩,
  refine ⟨⟨V ⊓ R, ⟨set.nonempty.mono this hU, V, R, rfl⟩⟩, this⟩,
end

lemma inf_mono_left {I : X.cl} : monotone (λ J : X.cl, J ⊓ I) :=
begin
  intros J K h,
  dsimp,
  simp_rw inf_comm,
  exact inf_mono_right h,
end

section refined

/-!
Given `h : I ≤ J`, `refined h U` is the unique element in `J` which `U` refined.
-/

def refined {I J : X.cl} (h : I ≤ J) (U : I) : J := classical.some (h U)

lemma refined_le {I J : X.cl} (h : I ≤ J) (U : I) : (U : set X) ≤ refined h U :=
  classical.some_spec (h U)

lemma refined_unique {I J : X.cl} (h : I ≤ J) (U : I) (V : J) : (U : set X) ≤ V →
  V = refined h U :=
begin
  intro hh,
  rcases I.nonempty U with ⟨x,hx⟩,
  rcases J.cover x with ⟨W,hW,h2⟩,
  rw [h2 V (hh hx), h2 (refined h U) (refined_le _ _ hx)],
end

@[simp]
lemma refined_id {I : X.cl} (U : I) : refined (le_refl I) U = U :=
begin
  symmetry,
  apply refined_unique,
  exact le_refl _,
end

@[simp]
lemma refined_comp {I J K : X.cl} (U : I) (h1 : I ≤ J) (h2 : J ≤ K) :
  refined (le_trans h1 h2) U = refined h2 (refined h1 U) := eq.symm $
refined_unique _ _ _ $ le_trans (refined_le h1 _) (refined_le _ _)

end refined

section proj

/-!
Given `I : X.cl`, `proj I` is the function `X → I` sending `x` to the unique
memeber of `I` in which it's contained.
-/

def proj_fun (I : X.cl) : X → I := λ x, classical.some (I.cover x)

lemma proj_fun_spec (I : X.cl) (x : X) : x ∈ (proj_fun I x : set X) :=
  (classical.some_spec (I.cover x)).1

lemma proj_fun_unique (I : X.cl) (x : X) (U : I) : x ∈ (U : set X) → U = proj_fun I x :=
begin
  intro h,
  rcases I.cover x with ⟨V,hV,hh⟩,
  rw [hh U h, hh (proj_fun I x) (proj_fun_spec _ _)],
end

lemma proj_fun_mem (I : X.cl) (x y : X) :
  x ∈ (proj_fun I y : set X) ↔ proj_fun I y = proj_fun I x :=
begin
  split,
  { intro h,
    exact proj_fun_unique _ _ _ h },
  { intro h,
    rw h,
    apply proj_fun_spec }
end

-- A description of the preimage of a set w.r.t. proj_fun
lemma proj_fun_preimage (I : X.cl) (S : set I) :
  proj_fun I ⁻¹' S = ⋃ (i : I) (hi : i ∈ S), (i : set X) :=
begin
  rw [← S.bUnion_of_singleton, set.preimage_Union],
  congr' 1,
  ext1 U,
  rw [set.bUnion_of_singleton, set.preimage_Union],
  congr' 1,
  ext h x,
  split,
  { intro hx,
    simp only [set.mem_preimage, set.mem_singleton_iff] at hx,
    rw ← hx, apply proj_fun_spec, },
  { intro h,
    rw proj_fun_unique _ _ _ h,
    simp [proj_fun_spec] }
end

-- A locally constant version of proj_fun
def proj (I : X.cl) : locally_constant X I :=
{ to_fun := proj_fun _,
  is_locally_constant := begin
    intros S,
    rw [proj_fun_preimage],
    apply is_open_bUnion,
    intros i hi,
    apply is_open,
  end}

-- Useful for functoriality of proj_fun's.
lemma proj_comp {I J : X.cl} (h : I ≤ J) (x : X) :
  refined h (proj I x) = proj J x :=
proj_fun_unique _ _ _ (refined_le _ _ $ proj_fun_spec _ _)

-- This shows the injectivity of the map
-- x ↦ (proj I x)_I
lemma eq_of_forall_proj_eq {x y : X} :
  (∀ I : X.cl, proj I x = proj I y) → x = y :=
begin
  intro h,
  suffices : x ∈ ({y} : set X), by simpa using this,
  have : totally_disconnected_space X, by apply_instance,
  rw totally_disconnected_space_iff_connected_component_singleton at this,
  rw [← this, connected_component_eq_Inter_clopen],
  rintros U ⟨⟨U,hU1,hU2⟩,rfl⟩,
  dsimp,
  by_cases ht : U = ⊤, { rw ht, tauto },
  have : Uᶜ.nonempty, by rwa set.nonempty_compl,
  let J := cl.of_clopen hU1 ⟨y,hU2⟩ this,
  specialize h J,
  suffices : proj J y = cl.of_clopen.mk,
  { change x ∈ ((of_clopen.mk : J) : set X),
    rw [← this, ← h],
    apply proj_fun_spec },
  symmetry,
  apply proj_fun_unique,
  exact hU2,
end

lemma exists_of_compat (Us : Π (I : X.cl), I)
  (compat : ∀ {I J : X.cl} (h : I ≤ J), refined h (Us I) = (Us J)) :
  ∃ x : X, ∀ I : X.cl, proj I x = Us I :=
begin
  have := is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
    (λ I, (Us I : set X)) (λ I J, ⟨common I J, _⟩) (λ I, I.nonempty _)
    (λ I, is_closed.compact (is_closed _)) (λ I, is_closed _),
  rcases this with ⟨x,hx⟩,
  { refine ⟨x,λ I, _⟩,
    symmetry,
    apply proj_fun_unique,
    refine hx _ ⟨I,rfl⟩ },
  dsimp only,
  rw [← compat (common_le_left : _ ≤ I), ← compat (common_le_right : _ ≤ J)],
  exact ⟨refined_le _ _, refined_le _ _⟩,
end

end proj

section pullback

variables {Y : Profinite.{u}} (f : Y ⟶ X)

def pullback : X.cl → Y.cl := λ I,
{ sets := { A | A.nonempty ∧ ∃ U : I, A = f ⁻¹' U },
  clopen := begin
    rintro ⟨A, h1, U, rfl⟩,
    exact ⟨is_open.preimage f.continuous (is_open _),
      is_closed.preimage f.continuous (is_closed _)⟩,
  end,
  nonempty := λ U, U.2.1,
  cover := begin
    intro y,
    rcases I.cover (f y) with ⟨U,hU1,hU2⟩,
    refine ⟨⟨f ⁻¹' U, ⟨y, hU1⟩, U, rfl⟩, hU1, _⟩,
    rintro ⟨V,⟨hV,V,rfl⟩⟩ hhV,
    suffices : V = U, by tidy,
    exact hU2 _ hhV,
  end }

variable {f}

lemma pullback_mono {I J : X.cl} (h : I ≤ J) : pullback f I ≤ pullback f J :=
begin
  rintro ⟨U,⟨hU,U,rfl⟩⟩,
  rcases h U with ⟨J,hJ⟩,
  refine ⟨⟨f ⁻¹' J, ⟨_, J, rfl⟩⟩, set.preimage_mono hJ⟩,
  exact set.nonempty.mono (set.preimage_mono hJ) hU,
end

lemma pullback_spec {I : X.cl} (U : pullback f I) : ∃! V : I, (U : set Y) = f ⁻¹' V :=
begin
  rcases U with ⟨U,⟨h,V,rfl⟩⟩,
  refine ⟨V, rfl, _⟩,
  intros W hW,
  rcases h with ⟨y,hy⟩,
  rcases I.cover (f y) with ⟨A,hA1,hA2⟩,
  dsimp at hW,
  have hy' := hy,
  rw hW at hy,
  rw [hA2 W hy, hA2 V hy'],
end

lemma pullback_proj {I : X.cl} (y : Y) : ((pullback f I).proj y : set Y) = f ⁻¹' (I.proj (f y)) :=
begin
  rcases pullback_spec ((pullback f I).proj y) with ⟨V,h1,h2⟩,
  erw h1,
  congr,
  apply proj_fun_unique,
  change y ∈ f ⁻¹' V,
  rw ← h1,
  apply proj_fun_spec,
end

lemma pullback_id {I : X.cl} : pullback (𝟙 X) I = I :=
begin
  ext S,
  dsimp [pullback],
  split,
  { rintro ⟨⟨z,hz⟩,⟨U,hU⟩⟩,
    simp [hU] },
  { intro h,
    refine ⟨I.nonempty ⟨S,h⟩, ⟨S,h⟩, rfl⟩ }
end

lemma pullback_comp {X Y Z : Profinite.{u}} {I : Z.cl} (f : X ⟶ Y) (g : Y ⟶ Z) :
  pullback (f ≫ g) I = pullback f (pullback g I) :=
begin
  ext S,
  dsimp [pullback],
  split,
  { rintro ⟨h1,U,hU⟩,
    refine ⟨h1,_⟩,
    rcases h1 with ⟨x,hx⟩,
    use g ⁻¹' (U : set Z),
    dsimp,
    refine ⟨_,_⟩,
    { rw hU at hx,
      simp at hx,
      refine ⟨f x, hx⟩ },
    { use U },
    { simpa using hU, } },
  { rintro ⟨⟨x,hx⟩,⟨U,hU1,⟨V,rfl⟩⟩,rfl⟩,
    refine ⟨⟨x,hx⟩,_⟩,
    refine ⟨V,_⟩,
    refl }
end

def map {I : X.cl} : pullback f I → I := λ U, classical.some (pullback_spec U)

lemma map_spec {I : X.cl} (U : pullback f I) : (U : set Y) = f ⁻¹' map U  :=
  (classical.some_spec (pullback_spec U)).1

lemma map_unique {I : X.cl} (U : pullback f I) (V : I) :
  (U : set Y) = f ⁻¹' V → V = map U :=
λ h, (classical.some_spec (pullback_spec U)).2 _ h

@[simp]
lemma map_refined_comm {I J : X.cl} (h : I ≤ J) (U : pullback f I) :
  map (refined (pullback_mono h : pullback f I ≤ _) U) = refined h (map U) :=
begin
  have := nonempty _ U,
  rcases this with ⟨y,hy⟩,
  have : refined h (map U) = proj _ (f y),
  { apply proj_fun_unique,
    apply refined_le,
    change y ∈ set.preimage f (map U),
    rw ← map_spec,
    assumption },
  rw this,
  apply proj_fun_unique,
  change y ∈ set.preimage f (map (refined (pullback_mono _) U) : set X),
  rw ← map_spec,
  exact refined_le _ _ hy,
end

end pullback

end cl

/-!
Up until this point, we didn't phrase anythign in terms of category theory.
We'll do this now.
-/
section categorical

variable (X)

@[simps]
def diagram : X.cl ⥤ Fintype :=
{ obj := λ I, Fintype.of I,
  map := λ I J h, cl.refined $ le_of_hom h,
  -- looks like some simp lemmas missing from Fintype TODO: Fix that...
  map_id' := λ X, by {ext1, change _ = x, simp},
  map_comp' := λ X Y Z f g, by {
    change (cl.refined _) = (cl.refined _) ∘ (cl.refined _),
    ext1,
    dsimp,
    erw ← cl.refined_comp } }

def Fintype.discrete (Z : Fintype) : topological_space Z := ⊥

local attribute [instance] Fintype.discrete

-- TODO: Move this.
@[simps]
def of_Fintype : Fintype ⥤ Profinite :=
{ obj := λ F, ⟨⟨F⟩⟩,
  map := λ A B f, ⟨f, continuous_of_discrete_topology⟩ }

@[simps]
def Fincone : limits.cone (X.diagram ⋙ of_Fintype) :=
{ X := X,
  π :=
  { app := λ I,
    { to_fun := cl.proj I,
      continuous_to_fun := (cl.proj I).continuous },
    naturality' := begin
      intros I J f,
      ext1 x,
      -- TODO: again, some simp lemmas missing...
      change J.proj x = (X.diagram ⋙ of_Fintype).map f (I.proj _),
      symmetry,
      apply cl.proj_fun_unique,
      simp,
      apply cl.refined_le,
      apply cl.proj_fun_spec
    end } }

instance is_iso_lift : is_iso ((limit_cone_cone_is_limit (X.diagram ⋙ of_Fintype)).lift X.Fincone) :=
is_iso_of_bijective _
begin
  split,
  { intros x y h,
    apply cl.eq_of_forall_proj_eq,
    intros I,
    apply_fun subtype.val at h,
    apply_fun (λ u, u I) at h,
    exact h },
  { let C := limit_cone_cone (X.diagram ⋙ of_Fintype),
    rintros (x : C.X.to_Top),
    have := cl.exists_of_compat (λ i : X.cl, x.val i)
      (λ I J f, _),
    { rcases this with ⟨x,hx⟩,
      refine ⟨x,_⟩,
      ext1,
      ext1 I,
      exact hx I },
    { change _ = C.π.app J _,
      erw ← C.w (hom_of_le f),
      refl } }
end

def Fincone_iso : X.Fincone ≅ limit_cone_cone _ :=
limits.cones.ext
(as_iso $ (limit_cone_cone_is_limit (X.diagram ⋙ of_Fintype)).lift X.Fincone) (λ I, rfl)

def Fincone_is_limit : limits.is_limit X.Fincone :=
limits.is_limit.of_iso_limit (limit_cone_cone_is_limit _) X.Fincone_iso.symm

variables {X} {Y : Profinite.{u}} (f : Y ⟶ X)

-- Don't use  this -- use change_cone instead.
def hom_cone : limits.cone (X.diagram ⋙ of_Fintype) :=
{ X := Y,
  π :=
  { app := λ I,
    { to_fun := cl.map ∘ (cl.pullback f I).proj,
      continuous_to_fun :=
        continuous.comp continuous_of_discrete_topology (locally_constant.continuous _) },
    naturality' := begin
      intros I J g,
      ext1 y,
      change cl.map ((cl.pullback f J).proj y) = cl.refined (le_of_hom g) _,
      dsimp at *,
      erw ← cl.map_refined_comm,
      symmetry,
      congr,
      apply cl.proj_fun_unique,
      apply cl.refined_le,
      apply cl.proj_fun_spec,
    end } }

-- Is this needed?
def cl.change : X.cl ⥤ Y.cl :=
{ obj := cl.pullback f,
  map := λ I J f, hom_of_le $ cl.pullback_mono $ le_of_hom f }

def change_cone (f : Y ⟶ X) (C : limits.cone (Y.diagram ⋙ of_Fintype)) :
  limits.cone (X.diagram ⋙ of_Fintype) :=
{ X := C.X,
  π :=
  { app := λ I, C.π.app (cl.pullback f I) ≫ ⟨cl.map⟩,
    naturality' := begin
      intros I J g,
      ext1,
      dsimp at *,
      have h : cl.pullback f _ ≤ _ := cl.pullback_mono (le_of_hom g),
      erw [← cl.map_refined_comm, ← C.w (hom_of_le h)],
      refl,
    end } }

theorem change_cone_lift : f = X.Fincone_is_limit.lift (change_cone f Y.Fincone) :=
begin
  refine X.Fincone_is_limit.uniq (change_cone f Y.Fincone) f _,
  intros I,
  ext1 y,
  change I.proj (f y) = cl.map _,
  symmetry,
  apply cl.proj_fun_unique,
  change _ ∈ f ⁻¹' ↑(cl.map (((cl.pullback f I).proj) y)),
  rw ← cl.map_spec,
  apply cl.proj_fun_spec,
end

def change_cone_id (C : limits.cone (X.diagram ⋙ of_Fintype)) :
  change_cone (𝟙 X) C ≅ C :=
limits.cones.ext (eq_to_iso rfl)
begin
  intros I,
  ext1,
  dsimp [change_cone] at *,
  symmetry,
  apply cl.map_unique,
  change _ = id ⁻¹' _,
  dsimp,
  rw cl.pullback_id,
end

def change_cone_id_Fincone : change_cone (𝟙 X) X.Fincone ≅ X.Fincone :=
change_cone_id _

def change_cone_comp {Z : Profinite.{u}} (g : Z ⟶ Y) (C : limits.cone (Z.diagram ⋙ of_Fintype)) :
  change_cone (g ≫ f) C ≅ change_cone f (change_cone g C) :=
limits.cones.ext (eq_to_iso rfl)
begin
  intros I,
  ext1 z,
  dsimp [change_cone] at *,
  symmetry,
  apply cl.map_unique,
  erw [set.preimage_comp, ← cl.map_spec, ← cl.map_spec, cl.pullback_comp],
end

def change_cone_comp_Fincone {Z : Profinite.{u}} (g : Z ⟶ Y) :
  change_cone (g ≫ f) Z.Fincone ≅ change_cone f (change_cone g Z.Fincone) :=
change_cone_comp _ _ _

end categorical

end Profinite
