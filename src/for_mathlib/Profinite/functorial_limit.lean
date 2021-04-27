import for_mathlib.arrow
import for_mathlib.Fintype.basic
import for_mathlib.Profinite.limits
import for_mathlib.Profinite.basic
import for_mathlib.Fintype.basic
import topology.locally_constant.basic
import category_theory.limits.functor_category

/-!
Let `X` and `Y` be profinite sets and `f : X ⟶ Y` a morphism.
We show:
1. That `X` is a limit of finite sets.
2. That `f` is a limit of morphisms of finite sets,
  when considered as an object in the arrow category.
-/

open_locale classical

universe u
open category_theory

noncomputable theory

namespace Profinite

/--
This is the type whose terms are decompositions of `X` into
disjoint unions of nonempty clopen sets.
This is endowed with a coercion to type, so one can write
`U : I` given `I : X.clopen_cover`, meaning that `U` is one of the sets
appearing in the clopen cover `I`.
-/
@[ext]
structure clopen_cover (X : Profinite.{u}) :=
(sets : set (set X))
(clopen : ∀ S : sets, is_clopen (S : set X))
(nonempty : ∀ S : sets, (S : set X).nonempty)
(cover : ∀ x : X, ∃! U: sets, x ∈ (U : set X))

namespace clopen_cover

variable {X : Profinite.{u}}

/-- 
Construct a term of `X.clopen_cover` given a nonempty clopen set of `X` whose
complement is nonempty.
-/
def of_clopen {U : set X} :
  is_clopen U → U.nonempty → Uᶜ.nonempty → X.clopen_cover := λ h1 h2 h3,
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

instance : has_coe_to_sort X.clopen_cover := ⟨Type*, λ I, I.sets⟩

instance {I : X.clopen_cover} : topological_space I := ⊥

lemma is_clopen {I : X.clopen_cover} (U : I) :
  is_clopen (U : set X) := (I.clopen _)

lemma is_open {I : X.clopen_cover} (U : I) :
  is_open (U : set X) := (I.clopen _).1

lemma is_closed {I : X.clopen_cover} (U : I) :
  is_closed (U : set X) := (I.clopen _).2

lemma eq_of_le {I : X.clopen_cover} (U V : I) : (U : set X) ≤ V → U = V :=
begin
  intro h,
  rcases (I.nonempty U) with ⟨y,hy⟩,
  rcases I.cover y with ⟨W,h1,h2⟩,
  rw [h2 U hy, h2 V (h hy)],
end

instance {I : X.clopen_cover} : fintype I :=
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

/-- The "trivial" clopen cover. -/
def top : X.clopen_cover :=
if h : _root_.nonempty X then
⟨{⊤}, by simp, begin
  rcases h with ⟨x⟩,
  rintro ⟨h,hh⟩,
  refine ⟨x,_⟩,
  simp only [set.mem_singleton_iff] at hh,
  simp [hh]
end,by tidy⟩
else
⟨∅,by simp, by simp, λ x, false.elim (h ⟨x⟩)⟩

lemma top_def : (top : X.clopen_cover) =
if h : _root_.nonempty X then
⟨{⊤}, by simp, begin
  rcases h with ⟨x⟩,
  rintro ⟨h,hh⟩,
  refine ⟨x,_⟩,
  simp only [set.mem_singleton_iff] at hh,
  simp [hh]
end, by tidy⟩
else
⟨∅, by simp, by simp, λ x, false.elim (h ⟨x⟩)⟩ := rfl

instance : has_top X.clopen_cover := ⟨top⟩
instance : inhabited X.clopen_cover := ⟨⊤⟩

/-- 
The "canonical" term of `clopen_cover.of_clopen`, whose underlying set is the given clopen set. 
-/
def of_clopen.mk {U : set X} {h1 : _root_.is_clopen U} {h2 : U.nonempty} {h3 : Uᶜ.nonempty} :
  of_clopen h1 h2 h3 := ⟨U, or.inl rfl⟩

/-- The coarsest common refinement of two clopen covers. -/
def common (I J : X.clopen_cover) : X.clopen_cover :=
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

/-- 
`le_rel f I J`, where `f : X ⟶ Y`, `I : X.clopen_cover` and
`J : Y.clopen_cover` means, mathematically, that
`I` refines the pullback of `J` with respect to `f`.
-/
def le_rel {X Y : Profinite.{u}} (f : X ⟶ Y)
  (I : X.clopen_cover) (J : Y.clopen_cover) : Prop :=
∀ U : I, ∃ V : J, (U : set X) ≤ f ⁻¹' V

lemma le_rel_top {X Y : Profinite.{u}} (f : X ⟶ Y) (I : X.clopen_cover) :
  le_rel f I ⊤ :=
begin
  change le_rel f I top,
  intros U,
  rcases I.nonempty U with ⟨x,hx⟩,
  rw top_def,
  refine ⟨⟨⊤,_⟩,λ x, by tauto⟩,
  split_ifs,
  { simp },
  { exact false.elim (h ⟨f x⟩) },
end

/-- 
Given `h : le_refl f I J`, this provides the canonical map `I → J`.
-/
def map {X Y : Profinite.{u}} {f : X ⟶ Y} {I : X.clopen_cover}
  {J : Y.clopen_cover} (h : le_rel f I J) : I → J :=
λ U, classical.some (h U)

lemma map_spec {X Y : Profinite.{u}} {f : X ⟶ Y} {I : X.clopen_cover}
  {J : Y.clopen_cover} (h : le_rel f I J) (U : I) :
  (U : set X) ≤ f ⁻¹' (map h U) := classical.some_spec (h U)

lemma map_unique {X Y : Profinite.{u}} {f : X ⟶ Y} {I : X.clopen_cover}
  {J : Y.clopen_cover} (h : le_rel f I J) (U : I) (V : J) :
  (U : set X) ≤ f ⁻¹' V → V = map h U :=
begin
  intro hh,
  rcases (I.nonempty U) with ⟨x,hx⟩,
  rcases J.cover (f x) with ⟨W,hW1,hW2⟩,
  rw [hW2 V (hh hx), hW2 (map h U) (map_spec _ _ hx)],
end

lemma le_rel_refl (I : X.clopen_cover) : le_rel (𝟙 X) I I := λ U, ⟨U, by simp⟩

lemma le_rel_comp {X Y Z : Profinite.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  {I : X.clopen_cover} {J : Y.clopen_cover} {K : Z.clopen_cover} :
  le_rel f I J → le_rel g J K → le_rel (f ≫ g) I K :=
begin
  intros h1 h2 U,
  rcases h1 U with ⟨V,hV⟩,
  rcases h2 V with ⟨W,hW⟩,
  refine ⟨W,le_trans hV _⟩,
  dsimp,
  conv_rhs { rw set.preimage_comp },
  exact set.preimage_mono hW,
end

@[simp]
lemma map_id {X : Profinite.{u}} {I : X.clopen_cover} (U : I) :
  map (le_rel_refl I) U = U :=
begin
  symmetry,
  apply map_unique,
  simp,
end

@[simp]
lemma map_comp {X Y Z : Profinite.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  {I : X.clopen_cover} {J : Y.clopen_cover} {K : Z.clopen_cover}
  (h1 : le_rel f I J) (h2 : le_rel g J K) (U : I) :
  map (le_rel_comp h1 h2) U = map h2 (map h1 U) :=
begin
  symmetry,
  apply map_unique,
  refine le_trans (map_spec h1 U) _,
  dsimp,
  conv_rhs {rw set.preimage_comp},
  apply set.preimage_mono,
  apply map_spec,
end


lemma common_le_rel_left {I J : X.clopen_cover} : le_rel (𝟙 _) (common I J) I :=
begin
  rintro ⟨U, ⟨U, A, B, rfl⟩⟩,
  refine ⟨A, set.inter_subset_left _ _⟩,
end

lemma common_le_rel_right {I J : X.clopen_cover} : le_rel (𝟙 _) (common I J) J :=
begin
  rintro ⟨U, ⟨U, A, B, rfl⟩⟩,
  refine ⟨B, set.inter_subset_right _ _⟩,
end

instance : semilattice_inf X.clopen_cover :=
{ inf := λ I J, common I J,
  le := λ I J, le_rel (𝟙 _) I J,
  le_refl := λ I, le_rel_refl _,
  le_trans := λ I J K h1 h2, by simpa using le_rel_comp h1 h2,
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
  inf_le_left := λ I J, common_le_rel_left,
  inf_le_right := λ I J, common_le_rel_right,
  le_inf := begin
    intros I J K h1 h2 U,
    rcases h1 U with ⟨A,hA⟩,
    rcases h2 U with ⟨B,hB⟩,
    simp only [set.preimage_id, Profinite.id_to_fun, set.le_eq_subset] at hA hB,
    obtain ⟨x,hx⟩ := I.nonempty U,
    refine ⟨⟨A ⊓ B, ⟨x, hA hx, hB hx⟩, A, B, rfl⟩, _⟩,
    simp only [set.preimage_id,
      Profinite.id_to_fun,
      set.subset_inter_iff,
      subtype.coe_mk,
      set.le_eq_subset,
      set.inf_eq_inter],
    refine ⟨hA,hB⟩,
  end }

lemma inf_mono_left {I J K : X.clopen_cover} : J ≤ K → J ⊓ I ≤ K ⊓ I :=
begin
  rintros h ⟨U,⟨hU,A,B,rfl⟩⟩,
  rcases h A with ⟨AA,hAA⟩,
  simp only [set.preimage_id, Profinite.id_to_fun, set.le_eq_subset] at *,
  have : (A : set X) ⊓ B ≤ AA ⊓ B := λ x ⟨h1,h2⟩, ⟨hAA h1,h2⟩,
  refine ⟨⟨AA ⊓ B,set.nonempty.mono this hU, AA, B, rfl⟩,this⟩,
end

lemma inf_mono_right {I J K : X.clopen_cover} : J ≤ K → I ⊓ J ≤ I ⊓ K :=
begin
  rintros h ⟨U,⟨hU,A,B,rfl⟩⟩,
  rcases h B with ⟨BB,hBB⟩,
  simp only [set.preimage_id, Profinite.id_to_fun, set.le_eq_subset] at *,
  have : (A : set X) ⊓ B ≤ A ⊓ BB := λ x ⟨h1,h2⟩, ⟨h1, hBB h2⟩,
  refine ⟨⟨A ⊓ BB, set.nonempty.mono this hU, A, BB, rfl⟩, this⟩
end

section pullback

variables {Y : Profinite.{u}} (f : Y ⟶ X)

/-- The pullback of a clopen cover w.r.t. a morphism. -/
def pullback : X.clopen_cover → Y.clopen_cover := λ I,
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

lemma pullback_mono {I J : X.clopen_cover} (h : I ≤ J) : pullback f I ≤ pullback f J :=
begin
  rintro ⟨U,⟨hU,U,rfl⟩⟩,
  rcases h U with ⟨J,hJ⟩,
  refine ⟨⟨f ⁻¹' J, ⟨_, J, rfl⟩⟩, set.preimage_mono hJ⟩,
  exact set.nonempty.mono (set.preimage_mono hJ) hU,
end

lemma pullback_spec {I : X.clopen_cover} (U : pullback f I) : ∃! V : I, (U : set Y) = f ⁻¹' V :=
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

-- TODO: Move if needed.
/-
lemma pullback_proj {I : X.clopen_cover} (y : Y) : ((pullback f I).proj y : set Y) = f ⁻¹' (I.proj (f y)) :=
begin
  rcases pullback_spec ((pullback f I).proj y) with ⟨V,h1,h2⟩,
  erw h1,
  congr,
  apply proj_fun_unique,
  change y ∈ f ⁻¹' V,
  rw ← h1,
  apply proj_fun_spec,
end
-/

lemma pullback_id {I : X.clopen_cover} : pullback (𝟙 X) I = I :=
begin
  ext S,
  dsimp [pullback],
  split,
  { rintro ⟨⟨z,hz⟩,⟨U,hU⟩⟩,
    simp [hU] },
  { intro h,
    refine ⟨I.nonempty ⟨S,h⟩, ⟨S,h⟩, rfl⟩ }
end

lemma pullback_comp {X Y Z : Profinite.{u}} {I : Z.clopen_cover} (f : X ⟶ Y) (g : Y ⟶ Z) :
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
      simp only [set.mem_preimage, function.comp_app] at hx,
      refine ⟨f x, hx⟩ },
    { use U },
    { simpa using hU, } },
  { rintro ⟨⟨x,hx⟩,⟨U,hU1,⟨V,rfl⟩⟩,rfl⟩,
    refine ⟨⟨x,hx⟩,_⟩,
    refine ⟨V,_⟩,
    refl }
end

lemma pullback_le_rel (I : X.clopen_cover) : le_rel f (pullback f I) I :=
begin
  rintros ⟨U,hU1,V,rfl⟩,
  refine ⟨V,le_refl _⟩,
end

lemma pullback_map_injective {B : Profinite} (f : X ⟶ B) (I : B.clopen_cover) :
  function.injective (clopen_cover.map I.pullback_le_rel : I.pullback f → I) :=
begin
  intros U V h,
  apply clopen_cover.eq_of_le,
  intros a ha,
  have hU := clopen_cover.map_spec (I.pullback_le_rel : clopen_cover.le_rel f _ _) U ha,
  rw h at hU,
  rcases (clopen_cover.pullback_spec V) with ⟨W,h1,h2⟩,
  rw h1,
  convert hU,
  apply clopen_cover.map_unique,
  refine le_of_eq h1,
end

end pullback

section proj

/-!
Given `I : X.cl`, `proj I` is the function `X → I` sending `x` to the unique
memeber of `I` in which it's contained.
-/

/-- The function underlying the canonical projection `X ⟶ I` for `I : X.clopen_cover`. -/
def proj_fun (I : X.clopen_cover) : X → I := λ x, classical.some (I.cover x)

lemma proj_fun_spec (I : X.clopen_cover) (x : X) : x ∈ (proj_fun I x : set X) :=
  (classical.some_spec (I.cover x)).1

lemma proj_fun_unique (I : X.clopen_cover) (x : X) (U : I) :
  x ∈ (U : set X) → U = proj_fun I x :=
begin
  intro h,
  rcases I.cover x with ⟨V,hV,hh⟩,
  rw [hh U h, hh (proj_fun I x) (proj_fun_spec _ _)],
end

lemma proj_fun_mem (I : X.clopen_cover) (x y : X) :
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
lemma proj_fun_preimage (I : X.clopen_cover) (S : set I) :
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

/-- A locally constant version of proj_fun -/
def proj (I : X.clopen_cover) : locally_constant X I :=
{ to_fun := proj_fun _,
  is_locally_constant := begin
    intros S,
    rw [proj_fun_preimage],
    apply is_open_bUnion,
    intros i hi,
    apply is_open,
  end}

lemma proj_map_comm {X Y : Profinite.{u}} {f : X ⟶ Y}
  {I : X.clopen_cover} {J : Y.clopen_cover} (h : le_rel f I J) (x : X) :
  map h (I.proj x) = J.proj (f x) :=
begin
  apply proj_fun_unique,
  change x ∈ f ⁻¹' (map h (I.proj x)),
  apply map_spec,
  apply proj_fun_spec,
end

/-- A version of `I.proj` as a morphism in `Profinite`. -/
def π (I : X.clopen_cover) : X ⟶ Fintype_to_Profinite.obj (Fintype.of I) :=
{ to_fun := proj _,
  continuous_to_fun := locally_constant.continuous _ }

/-- This lemma shows the injectivity of the map `x ↦ (proj I x)_I` -/
lemma eq_of_forall_proj_eq {x y : X} :
  (∀ I : X.clopen_cover, proj I x = proj I y) → x = y :=
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
  let J := of_clopen hU1 ⟨y,hU2⟩ this,
  specialize h J,
  suffices : proj J y = of_clopen.mk,
  { change x ∈ ((of_clopen.mk : J) : set X),
    rw [← this, ← h],
    apply proj_fun_spec },
  symmetry,
  apply proj_fun_unique,
  exact hU2,
end

/-- This lemma shows the surjectivity of the map from `X` to the limit of `I : X.clopen_cover`. -/
lemma exists_of_compat (Us : Π (I : X.clopen_cover), I)
  (compat : ∀ {I J : X.clopen_cover} (h : I ≤ J), map h (Us I) = (Us J)) :
  ∃ x : X, ∀ I : X.clopen_cover, proj I x = Us I :=
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
  rw [← compat (inf_le_left : I ⊓ J ≤ I), ← compat (inf_le_right : I ⊓ J ≤ J)],
  refine ⟨map_spec _ _, map_spec _ _⟩,
end

end proj

end clopen_cover

section limit_rep

variables (X : Profinite.{u})

/-- The diagram indexed by `X.clopen_cover` whose limit is isomorphic to `X`. -/
def diagram : X.clopen_cover ⥤ Fintype.{u} :=
{ obj := λ I, Fintype.of I,
  map := λ I J h, clopen_cover.map $ le_of_hom h,
  map_id' := λ I, by {ext1, erw [clopen_cover.map_id], simp },
  map_comp' := λ I J K f g,
    by {ext1, simp only [Fintype.comp_apply], erw ← clopen_cover.map_comp, refl, } }

/-- The limit cone exhibiting `X` as a limit of `X.diagram`. -/
def Fincone : limits.cone (X.diagram ⋙ Fintype_to_Profinite) :=
{ X := X,
  π :=
  { app := λ I, I.π,
    naturality' := begin
      intros I J j,
      ext1 x,
      symmetry,
      apply clopen_cover.proj_fun_unique,
      simp only [Profinite.id_to_fun,
        id.def,
        category_theory.functor.comp_map,
        Profinite.comp_to_fun,
        function.comp_app,
        category_theory.functor.const.obj_map],
      apply clopen_cover.map_spec,
      apply clopen_cover.proj_fun_spec,
    end } }

instance is_iso_lift :
  is_iso ((limit_cone (X.diagram ⋙ Fintype_to_Profinite)).is_limit.lift X.Fincone) :=
is_iso_of_bijective _
begin
  split,
  { intros x y h,
    apply clopen_cover.eq_of_forall_proj_eq,
    intros I,
    apply_fun (λ u, u.val I) at h,
    exact h },
  { let C := (limit_cone (X.diagram ⋙ Fintype_to_Profinite)).cone,
    rintros (x : C.X.to_Top),
    have := clopen_cover.exists_of_compat (λ I : X.clopen_cover, x.val I) (λ I J f, _),
    { rcases this with ⟨x,hx⟩,
      refine ⟨x,_⟩,
      ext1, ext1 I,
      exact hx I },
    { change _ = C.π.app J _,
      erw ← C.w (hom_of_le f),
      refl } }
end

/-- 
The isomorphism of cones between `X.Fincone` and 
`limit_cone (X.diagram ⋙ Fintype_to_Profinite)`. 
-/
def Fincone_iso : X.Fincone ≅ (limit_cone _).cone :=
limits.cones.ext (as_iso $ (limit_cone _).is_limit.lift _) (λ _, rfl)

/-- 
`X.Fincone` is indeed a limit cone. 
-/
def Fincone_is_limit : limits.is_limit X.Fincone :=
limits.is_limit.of_iso_limit (limit_cone_cone_is_limit _) X.Fincone_iso.symm

variables {X} {Y : Profinite.{u}}

/-- 
Change a cone over `Y.diagram ⋙ Fintype_to_Profinite` 
with respect to a morphism `f : X ⟶ Y`.
This is used to obtain the functorial properties of the `X.Fincone` constructions.
-/
def change_cone (f : Y ⟶ X) (C : limits.cone (Y.diagram ⋙ Fintype_to_Profinite)) :
  limits.cone (X.diagram ⋙ Fintype_to_Profinite) :=
{ X := C.X,
  π :=
  { app := λ I, C.π.app (clopen_cover.pullback f I) ≫
      ⟨clopen_cover.map (clopen_cover.pullback_le_rel _)⟩,
    naturality' := begin
      intros I J g,
      ext1,
      dsimp [diagram] at *,
      have h : clopen_cover.pullback f _ ≤ _ := clopen_cover.pullback_mono (le_of_hom g),
      erw [← C.w (hom_of_le h)],
      dsimp [Fintype_to_Profinite],
      simp_rw [← clopen_cover.map_comp],
      refl,
    end } }

theorem change_cone_lift (f : Y ⟶ X) : f = X.Fincone_is_limit.lift (change_cone f Y.Fincone) :=
begin
  apply X.Fincone_is_limit.uniq (change_cone f Y.Fincone) f,
  intros I,
  ext1 y,
  change I.proj (f y) = _,
  dsimp [change_cone],
  symmetry,
  apply clopen_cover.proj_fun_unique,
  apply clopen_cover.map_spec,
  apply clopen_cover.proj_fun_spec,
end

/-- Changing a cone by an identity morphism results in a cone isomorphic to the given one. -/
def change_cone_id (C : limits.cone (X.diagram ⋙ Fintype_to_Profinite)) :
  change_cone (𝟙 X) C ≅ C :=
limits.cones.ext (eq_to_iso rfl)
begin
  intros I,
  ext1,
  dsimp [change_cone] at *,
  symmetry,
  apply clopen_cover.map_unique,
  erw clopen_cover.pullback_id,
  simp,
end

/-- The compatibility of `change_cone` with respect to composition of morphisms. -/
def change_cone_comp {Z : Profinite.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
  (C : limits.cone (Z.diagram ⋙ Fintype_to_Profinite)) :
  change_cone (g ≫ f) C ≅ change_cone f (change_cone g C) :=
limits.cones.ext (eq_to_iso rfl)
begin
  intros I,
  ext1,
  dsimp [change_cone] at *,
  symmetry,
  apply clopen_cover.map_unique,
  rw clopen_cover.pullback_comp,
  refine le_trans (clopen_cover.map_spec (clopen_cover.pullback_le_rel _) _) _,
  nth_rewrite 1 set.preimage_comp,
  apply set.preimage_mono,
  apply clopen_cover.map_spec,
end

end limit_rep

namespace arrow

variable (f : arrow Profinite.{u})

/-- 
A gadget used to show that any arrow in `Profinite` can be expressed as a 
limit of arrows of `Fintype`s. 
This will be used as the category indexing the limit.
-/
@[nolint has_inhabited_instance]
structure index_cat : Type u :=
(left : f.left.clopen_cover)
(right : f.right.clopen_cover)
(compat : left.le_rel f.hom right)

namespace index_cat

variable {f}

/-- Morphisms for `index_cat`. -/
@[nolint has_inhabited_instance]
structure hom (A B : index_cat f) : Type u :=
(left : A.left ≤ B.left)
(right : A.right ≤ B.right)

instance : category (index_cat f) :=
{ hom := hom,
  id := λ A, ⟨le_refl _, le_refl _⟩,
  comp := λ A B C f g , ⟨le_trans f.left g.left, le_trans f.right g.right⟩,
  id_comp' := λ A B f, by {cases f, refl},
  comp_id' := λ A B f, by {cases f, refl},
  assoc' := λ A B C D f g h, by {cases f, cases g, cases h, refl} }

/-- 
Make a term of `index_cat` given a clopen cover of a target of the arrow.
This is done fuunctorially.
-/
def mk_right : f.right.clopen_cover ⥤ index_cat f :=
{ obj := λ I,
  { left := clopen_cover.pullback f.hom I,
    right := I,
    compat := clopen_cover.pullback_le_rel _ },
  map := λ I J f,
  { left := clopen_cover.pullback_mono $ le_of_hom f,
    right := le_of_hom f } }

/-- 
Make a term of `index_cat` given a clopen cover of a source of the arrow.
This is done fuunctorially.
-/
def mk_left : f.left.clopen_cover ⥤ index_cat f :=
{ obj := λ I,
  { left := I,
    right := ⊤,
    compat := clopen_cover.le_rel_top _ _ },
  map := λ I J f,
  { left := le_of_hom f,
    right := clopen_cover.le_rel_top _ _ } }

/-- 
A combination of `mk_left` and `mk_right`.
-/
def make : f.left.clopen_cover ⥤ f.right.clopen_cover ⥤ index_cat f :=
{ obj := λ I,
  { obj := λ J,
    { left := I ⊓ clopen_cover.pullback f.hom J,
      right := J,
      compat := begin
        dsimp,
        have : f.hom = 𝟙 _ ≫ f.hom, by simp,
        rw this,
        refine clopen_cover.le_rel_comp _ (clopen_cover.pullback_le_rel _),
        simp only [category_theory.category.id_comp],
        dsimp,
        exact (inf_le_right : I ⊓ clopen_cover.pullback f.hom J ≤ _)
      end },
    map := λ I J g,
    { left := clopen_cover.inf_mono_right $ clopen_cover.pullback_mono $ le_of_hom g,
      right := le_of_hom g } },
  map := λ I J g,
  { app := λ K,
    { left := clopen_cover.inf_mono_left $ le_of_hom g,
      right := le_refl _ } } }.

end index_cat

/-- 
The diagram whose limit is a given arrow in `Profinite`.
-/
def diagram : index_cat f ⥤ arrow Fintype.{u} :=
{ obj := λ A,
  { left := Fintype.of A.left,
    right := Fintype.of A.right,
    hom := clopen_cover.map A.compat },
  map := λ A B g,
  { left := clopen_cover.map g.left,
    right := clopen_cover.map g.right,
    w' := begin
      ext1 x,
      dsimp,
      simp_rw ← clopen_cover.map_comp,
      refl,
    end },
  map_id' := begin
    intros A,
    ext1,
    all_goals {
      dsimp,
      ext1,
      erw clopen_cover.map_id,
      refl },
  end,
  map_comp' := begin
    intros A B C f g,
    ext1,
    all_goals {
      ext1,
      dsimp,
      erw ← clopen_cover.map_comp,
      refl },
  end }

/-- An abbreviation for `diagram f ⋙ Fintype_to_Profinite.map_arrow`. -/
abbreviation diagram' : index_cat f ⥤ arrow Profinite := diagram f ⋙ Fintype_to_Profinite.map_arrow

/-- The diagram of profinite sets obtained from the sources of `diagram'`. -/
abbreviation left_diagram : index_cat f ⥤ Profinite := diagram' f ⋙ arrow.left_func

/-- The diagram of profinite sets obtained from the targets of `diagram'`. -/
abbreviation right_diagram : index_cat f ⥤ Profinite := diagram' f ⋙ arrow.right_func

/-- The usual limit cone over `diagram' f`. -/
def limit_cone : limits.limit_cone (diagram' f) :=
arrow.limit_cone _ (limit_cone $ left_diagram _) (limit_cone $ right_diagram _)

/-- 
The cone which we want to show is a limit cone of `diagram' f`.
Its cone point is the given arrow `f`.
-/
def Fincone : limits.cone (diagram' f) :=
{ X := f,
  π :=
  { app := λ Is,
    { left := clopen_cover.π _,
      right := clopen_cover.π _,
      w' := begin
        ext1 x,
        dsimp [diagram, clopen_cover.π, Fintype_to_Profinite],
        erw clopen_cover.proj_map_comm,
      end },
    naturality' := begin
      intros Is Js f,
      ext1;
      ext1 x,
      { dsimp [clopen_cover.π, diagram, Fintype_to_Profinite],
        erw clopen_cover.proj_map_comm,
        refl },
      { dsimp [clopen_cover.π, diagram, Fintype_to_Profinite],
        erw clopen_cover.proj_map_comm,
        refl }
    end } }.

instance is_iso_lift_left : is_iso ((limit_cone f).is_limit.lift (Fincone f)).left :=
is_iso_of_bijective _
begin
  split,
  { intros x y h,
    apply clopen_cover.eq_of_forall_proj_eq,
    intros I,
    apply_fun subtype.val at h,
    let II := index_cat.mk_left.obj I,
    apply_fun (λ f, f II) at h,
    exact h },
 { intros x,
    cases x with x hx,
    dsimp at *,
    let Us : Π (I : f.left.clopen_cover), I := λ U, x (index_cat.mk_left.obj U),
    rcases clopen_cover.exists_of_compat Us _ with ⟨y,hy⟩,
    { refine ⟨y,_⟩,
      ext Is : 2,
      dsimp at *,
      change clopen_cover.proj _ _ = _,
      have : x Is = Us Is.left,
      { let ff : Is ⟶ index_cat.mk_left.obj Is.left := ⟨le_refl _,clopen_cover.le_rel_top _ _⟩,
        dsimp [Us],
        rw ← hx ff,
        apply clopen_cover.map_unique,
        simp },
      rw this,
      apply hy },
    { intros I J h,
      specialize hx (index_cat.mk_left.map $ hom_of_le h),
      exact hx } }
end

instance is_iso_lift_right : is_iso ((limit_cone f).is_limit.lift (Fincone f)).right :=
is_iso_of_bijective _
begin
  split,
  { intros x y h,
    apply clopen_cover.eq_of_forall_proj_eq,
    intros I,
    apply_fun subtype.val at h,
    let II := index_cat.mk_right.obj I,
    apply_fun (λ f, f II) at h,
    change clopen_cover.proj _ _ = clopen_cover.proj _ _ at h,
    have hII : II.right ≤ I := le_refl _,
    erw [← clopen_cover.proj_map_comm hII, h, clopen_cover.proj_map_comm],
    simp },
  { intros x,
    cases x with x hx,
    let Us : Π (I : f.right.clopen_cover), I := λ U, x (index_cat.mk_right.obj U),
    rcases clopen_cover.exists_of_compat Us _ with ⟨y,hy⟩,
    { refine ⟨y,_⟩,
      ext Is : 2,
      dsimp at *,
      change clopen_cover.proj _ _ = _,
      have : x Is = Us Is.right,
      { let ff : Is ⟶ index_cat.mk_right.obj Is.right := ⟨_,le_refl _⟩,
        dsimp [Us],
        rw ← hx ff,
        apply clopen_cover.map_unique,
        simp only [set.preimage_id, Profinite.id_to_fun, set.le_eq_subset],
        dsimp [index_cat.mk_right],
        intros U,
        rcases Is.compat U with ⟨V,hV⟩,
        refine ⟨⟨_,_,V,rfl⟩,_⟩,
        rcases Is.left.nonempty U with ⟨z,hz⟩,
        refine ⟨z, hV hz⟩,
        simpa },
      rw this,
      apply hy },
    { intros I J h,
      specialize hx (index_cat.mk_right.map $ hom_of_le h),
      exact hx } }
end

-- sanity check
example : is_iso ((limit_cone f).is_limit.lift (Fincone f)) := by apply_instance

/-- The isomorphism between `Fincone f` and the cone of the limit cone `(limit_cone f)`. -/
def Fincone_iso : Fincone f ≅ (limit_cone f).cone :=
limits.cones.ext (as_iso ((limit_cone f).is_limit.lift (Fincone f))) (λ I, rfl)

/-- `Fincone f` is indeed a limit cone. -/
def Fincone_is_limit : limits.is_limit (Fincone f) :=
limits.is_limit.of_iso_limit (limit_cone f).is_limit (Fincone_iso f).symm

/--
If `f` is surjective, then the terms in the diagram whose limit is `f` are all surjective as well.
-/
lemma surjective_of_surjective (surj : function.surjective f.hom) (I : index_cat f) :
  function.surjective ((diagram f).obj I).hom :=
begin
  intros U,
  change ↥I.right at U,
  rcases I.right.nonempty U with ⟨x,hx⟩,
  rcases surj x with ⟨y,rfl⟩,
  let V : ↥(clopen_cover.pullback f.hom I.right) :=
    ⟨f.hom ⁻¹' (U : set f.right),⟨y,hx⟩,_,rfl⟩,
  rcases clopen_cover.nonempty _ V with ⟨z,hz⟩,
  use clopen_cover.proj _ z,
  dsimp [diagram],
  erw clopen_cover.proj_map_comm,
  symmetry,
  apply clopen_cover.proj_fun_unique,
  exact hz,
end

end arrow

end Profinite
