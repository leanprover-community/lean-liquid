import .Profinite
import topology.category.Profinite
import topology.locally_constant.basic
import category_theory.Fintype
import category_theory.limits.creates

noncomputable theory

namespace Profinite

open category_theory

universe u

variables (X : Profinite.{u})

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
      exact false.elim (hhV hx),
    },
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

instance is_iso_lift : is_iso ((limit_cone_is_limit (X.diagram ⋙ of_Fintype)).lift X.Fincone) :=
is_iso_of_bijective _
begin
  split,
  { intros x y h,
    apply cl.eq_of_forall_proj_eq,
    intros I,
    apply_fun subtype.val at h,
    apply_fun (λ u, u I) at h,
    exact h },
  { let C := limit_cone (X.diagram ⋙ of_Fintype),
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

def Fincone_iso : X.Fincone ≅ limit_cone _ :=
limits.cones.ext
(as_iso $ (limit_cone_is_limit (X.diagram ⋙ of_Fintype)).lift X.Fincone) (λ I, rfl)

def Fincone_is_limit : limits.is_limit X.Fincone :=
limits.is_limit.of_iso_limit (limit_cone_is_limit _) X.Fincone_iso.symm

end categorical

end Profinite
