import .Profinite
import category_theory.Fintype
import topology.locally_constant.basic

/-!
This file proves that every profinite set 
can be expressed as a limit of finite sets in a
*functorial* way.

Some of the code in this file was inspired by the 
`Profinite2` branch of mathlib by C. Sönne and B. Mehta.
-/

universes v u

open category_theory
open category_theory.limits

noncomputable theory

namespace Profinite

structure clopen_cover (X : Profinite) :=
(sets : set (set X))
--(finite : sets.finite) -- follows from compactness, see fintype instance below
(clopen : ∀ U : sets, is_clopen (U : set X))
(nonempty : ∀ U : sets, (U : set X).nonempty)
(disjoint : ∀ U V : sets, (U ⊓ V : set X).nonempty → U = V)
(cover' : ⋃₀ sets = ⊤)

variables {X Y : Profinite.{u}}

namespace clopen_cover

instance : has_coe_to_sort X.clopen_cover := ⟨Type*, λ I, I.sets⟩

lemma cover (I : X.clopen_cover) : (⋃ (i : I), (i : set X)) = ⊤ :=
by simpa [set.sUnion_eq_Union] using I.cover'

instance {I : X.clopen_cover} : fintype I :=
begin
  have h : _root_.is_compact (⊤ : set X) := compact_univ,
  rw compact_iff_finite_subcover at h,
  specialize h (λ i : I, i) (λ i, (I.clopen _).1) I.cover.symm.subset,
  let S := classical.some h,
  let hS := classical.some_spec h,
  refine ⟨S,_⟩,
  intros U,
  rcases I.nonempty U with ⟨x,hx⟩,
  specialize hS (by tauto : x ∈ ⊤),
  rcases hS with ⟨V,⟨W,rfl⟩,W,⟨(h1 : _ ∈ S),rfl⟩,h2⟩,
  dsimp at h2,
  suffices : U = W, by rwa this,
  apply I.disjoint,
  refine ⟨x,hx,h2⟩,
end

instance : inhabited X.clopen_cover :=
begin
  by_cases _root_.nonempty X,
  { refine ⟨⟨{⊤},_,_,_,_⟩⟩,
    { rintros ⟨U,hU⟩, refine ⟨_,_⟩,
      any_goals {dsimp,
        simp only [set.mem_singleton_iff, set.top_eq_univ] at hU,
        rw hU },
      exact is_open_univ,
      exact is_closed_univ },
    { rintros ⟨U,hU⟩,
      simp only [set.mem_singleton_iff, set.top_eq_univ] at hU,
      simp only [hU],
      cases h with x,
      refine ⟨x,by tauto⟩ },
    { rintros ⟨U,hU⟩ ⟨V,hV⟩ -,
      simp only [set.mem_singleton_iff, set.top_eq_univ] at hU hV,
      ext1,
      simp [hV,hU] },
    { simp } },
  refine ⟨⟨∅,_,_,_,_⟩⟩,
  any_goals { rintros ⟨_,h⟩, refine false.elim h },
  simp,
  symmetry,
  rw set.eq_empty_iff_forall_not_mem,
  intros x c,
  refine h ⟨x⟩,
end

instance {I : X.clopen_cover} : topological_space I := ⊥

instance : preorder X.clopen_cover :=
{ le := λ I J, ∀ U : I, ∃ V : J, (U : set X) ≤ V,
  le_refl := λ I U, ⟨U,le_refl _⟩,
  le_trans := begin
    intros I J K h1 h2 U,
    obtain ⟨V,hV⟩ := h1 U,
    obtain ⟨W,hW⟩ := h2 V,
    exact ⟨W, le_trans hV hW⟩
  end }

def pullback_obj (f : X ⟶ Y) : Y.clopen_cover → X.clopen_cover := λ I,
{ sets := { U | (∃ V : I, f⁻¹' V = U) ∧ (U : set X).nonempty },
  clopen := begin
    rintro ⟨U,⟨V,rfl⟩,h⟩,
    refine ⟨is_open.preimage f.2 (I.clopen _).1, is_closed.preimage f.2 (I.clopen _).2⟩,
  end,
  nonempty := λ U, U.2.2,
  disjoint := begin
    rintro ⟨U,⟨U,rfl⟩,hU⟩ ⟨V,⟨V,rfl⟩,hV⟩ ⟨x,hx1,hx2⟩,
    simp only [set.mem_preimage, subtype.coe_mk] at hx1 hx2,
    simp [I.disjoint U V ⟨f x, hx1, hx2⟩],
  end,
  cover' := begin
    have h := I.cover',
    erw set.eq_univ_iff_forall at *,
    intros x,
    rcases h (f x) with ⟨V,hV,hx⟩,
    exact ⟨f ⁻¹' V,⟨⟨⟨V,hV⟩,rfl⟩,⟨x,hx⟩⟩,hx⟩,
  end }.

lemma pullback_mono (f : X ⟶ Y) : monotone (pullback_obj f) :=
begin
  intros I J hh,
  rintro ⟨U,⟨U,rfl⟩,h⟩,
  rcases hh U with ⟨V,h1⟩,
  use f ⁻¹' (V : set Y),
  { exact ⟨⟨V,rfl⟩, set.nonempty.mono (set.preimage_mono h1) h⟩ },
  { exact set.preimage_mono h1, },
end

def pullback (f : X ⟶ Y) : Y.clopen_cover ⥤ X.clopen_cover :=
{ obj := pullback_obj f,
  map := λ I J g, hom_of_le $ pullback_mono _ (le_of_hom g) }

def of_clopen (U : set X) (h1 : U.nonempty) (h2 : Uᶜ.nonempty) (h : is_clopen U) :
  X.clopen_cover :=
{ sets := {U, Uᶜ},
  clopen := begin
    rintros ⟨V,hV|hV⟩,
    { dsimp,
      rwa hV },
    { dsimp,
      simp only [set.mem_singleton_iff] at hV,
      rw hV,
      refine ⟨_,_⟩,
      { rw is_open_compl_iff, exact h.2 },
      { rw is_closed_compl_iff, exact h.1} }
  end,
  nonempty := begin
    rintros ⟨V,hV|hV⟩,
    { simpa [hV] },
    { simp only [set.mem_singleton_iff] at hV,
      simpa [hV] },
  end,
  disjoint := begin
    rintro ⟨A,hA|hA⟩ ⟨B,hB|hB⟩ ⟨x,hx⟩; ext1; dsimp,
    any_goals { simp only [set.mem_singleton_iff] at hA hB },
    any_goals { rw [hA,hB] },
    { dsimp at hx,
      rw [hA, hB] at hx,
      exact false.elim (hx.2 hx.1) },
    { dsimp at hx,
      rw [hA, hB] at hx,
      exact false.elim (hx.1 hx.2) },
  end,
  cover' := begin
    erw set.eq_univ_iff_forall,
    intros x,
    by_cases x ∈ (U : set X),
    exact ⟨U,or.inl rfl, h⟩,
    exact ⟨Uᶜ, or.inr rfl, h⟩,
  end}.

def of_clopen.mk {U : set X} {h1 : U.nonempty} {h2 : Uᶜ.nonempty} {h : is_clopen U} :
  of_clopen U h1 h2 h := ⟨U, or.inl rfl⟩

def common_refinement (I J : X.clopen_cover) : X.clopen_cover :=
{ sets := { U | U.nonempty ∧ ∃ (A : I) (B : J), U = A ∩ B },
  clopen := begin
    rintro ⟨U,hU,⟨A,B,rfl⟩⟩,
    exact ⟨is_open_inter (I.clopen A).1 (J.clopen B).1,
      is_closed_inter (I.clopen A).2 (J.clopen B).2⟩,
  end,
  nonempty := λ U, U.2.1,
  disjoint := begin
    rintros ⟨U,hU,⟨A,B,rfl⟩⟩ ⟨V,hV,⟨C,D,rfl⟩⟩ ⟨x,⟨h1,h2⟩,h3,h4⟩,
    ext1,
    dsimp,
    erw I.disjoint A C ⟨x,h1,h3⟩,
    erw J.disjoint B D ⟨x,h2,h4⟩,
  end,
  cover' := begin
    have hI := I.cover,
    have hJ := J.cover,
    erw set.eq_univ_iff_forall at *,
    intros x,
    rcases hI x with ⟨A,⟨A,rfl⟩,hxA⟩,
    rcases hJ x with ⟨B,⟨B,rfl⟩,hxB⟩,
    dsimp at *,
    refine ⟨A ∩ B,⟨⟨x,hxA,hxB⟩, ⟨A, B, rfl⟩⟩,hxA,hxB⟩,
  end }

lemma common_refinement.le_left {I J : X.clopen_cover} : common_refinement I J ≤ I :=
begin
  rintros ⟨U,⟨h1,⟨A,B,rfl⟩⟩⟩,
  exact ⟨A,set.inter_subset_left _ _⟩,
end

lemma common_refinement.le_right {I J : X.clopen_cover} : common_refinement I J ≤ J :=
begin
  rintros ⟨U,⟨h1,⟨A,B,rfl⟩⟩⟩,
  exact ⟨B,set.inter_subset_right _ _⟩,
end

def common_refinement.fst {I J : X.clopen_cover} : common_refinement I J ⟶ I :=
hom_of_le $ common_refinement.le_left

def common_refinement.snd {I J : X.clopen_cover} : common_refinement I J ⟶ J :=
hom_of_le $ common_refinement.le_right

end clopen_cover

def refines {I J : X.clopen_cover} (f : I ≤ J) (U : I) : J := classical.some $ f U

lemma refines_spec {I J : X.clopen_cover} (f : I ≤ J) (U : I) : (U : set X) ≤ refines f U :=
  classical.some_spec (f U)

lemma refines_unique {I J : X.clopen_cover} (f : I ≤ J) (U : I) (V : J) :
  (U : set X) ≤ V → V = refines f U :=
λ h, J.disjoint _ _ (set.nonempty.mono (set.subset_inter h (refines_spec _ _)) (I.nonempty U))

@[simp]
lemma refines_refl (I : X.clopen_cover) (U : I) : refines (le_refl _) U = U :=
(refines_unique (le_refl _) U U $ le_refl _).symm

@[simp]
lemma refines_trans {I J K : X.clopen_cover} (f : I ≤ J) (g : J ≤ K) (U : I) :
  refines (le_trans f g) U = refines g (refines f U) := eq.symm $
refines_unique _ _ _ $ le_trans (refines_spec f U) (refines_spec _ _)

def diagram : X.clopen_cover ⥤ Profinite :=
{ obj := λ I, ⟨⟨I⟩⟩,
  map := λ I J f, ⟨λ U, refines (le_of_hom f) U, continuous_of_discrete_topology⟩,
  map_id' := begin
    intros I,
    ext1,
    dsimp,
    erw refines_refl,
    refl,
  end,
  map_comp' := begin
    rintros I J K h1 h2,
    ext1,
    dsimp,
    erw refines_trans,
    refl,
  end }

lemma exists_unique_mem (x : X) (I : X.clopen_cover) : ∃! U : I, x ∈ (U : set X) :=
begin
  have : x ∈ ⋃₀ I.sets, by simp [I.cover'],
  rcases this with ⟨U,hU,hx⟩,
  exact ⟨⟨U,hU⟩,hx, λ V hV, I.disjoint _ _ ⟨x,hV,hx⟩⟩,
end

def proj_fun (I : X.clopen_cover) : X → diagram.obj I := λ x, classical.some $ exists_unique_mem x I

@[simp]
lemma proj_fun_spec (I : X.clopen_cover) (x : X) (U : I) :
  proj_fun I x = U ↔ x ∈ (U : set X) :=
begin
  cases classical.some_spec (exists_unique_mem x I) with h1 h2,
  refine ⟨_,λ h, (h2 _ h).symm⟩,
  intro h,
  dsimp at h2,
  specialize h2 U,
  change x ∈ (proj_fun I x).1 at h1,
  rwa h at h1
end

lemma proj_fun_preimage (I : X.clopen_cover) (U : set I) :
  proj_fun I ⁻¹' U = ⋃ (i : I) (hi : i ∈ U), (i : set X) :=
begin
  erw [← U.bUnion_of_singleton, set.preimage_Union],
  congr' 1,
  tidy,
end

def proj_locally_constant (I : X.clopen_cover) : locally_constant X I :=
{ to_fun := proj_fun I,
  is_locally_constant := begin
    intros U,
    rw [proj_fun_preimage],
    apply is_open_bUnion,
    rintros i hi,
    exact (I.clopen i).1,
  end }

def proj (I : X.clopen_cover) : X ⟶ ⟨⟨I⟩⟩ :=
  ⟨proj_locally_constant I, (proj_locally_constant I).continuous⟩

@[simp]
lemma proj_comp_map {I J : X.clopen_cover} (f : I ⟶ J) :
  proj I ≫ diagram.map f = proj J :=
begin
  ext1 x,
  change diagram.map f (proj_fun _ _) = proj_fun _ _,
  symmetry,
  rw proj_fun_spec,
  apply refines_spec,
  erw ← proj_fun_spec,
end

theorem eq_of_proj_eq (x y : X) : (∀ I : X.clopen_cover, proj I x = proj I y) → x = y :=
begin
  intros h,
  suffices : x ∈ ({y} : set X), by simpa using this,
  have : totally_disconnected_space X, by apply_instance,
  rw totally_disconnected_space_iff_connected_component_singleton at this,
  rw [← this, connected_component_eq_Inter_clopen],
  rintros U ⟨⟨U,hU1,hU2⟩,rfl⟩,
  dsimp,
  by_cases ht : U = ⊤,
  { rw ht, tauto },
  have : Uᶜ.nonempty, by rwa set.nonempty_compl,
  let J := clopen_cover.of_clopen U ⟨y,hU2⟩ this hU1,
  specialize h J,
  suffices : proj J y = clopen_cover.of_clopen.mk,
  { erw [proj_fun_spec, this] at h, assumption },
  erw proj_fun_spec,
  assumption,
end

theorem exists_of_compat (is : Π (I : X.clopen_cover), I)
  (compat : ∀ (I J : X.clopen_cover) (f : I ≤ J), refines f (is _) = is _) :
  ∃ x : X, ∀ I, proj I x = is _ :=
begin
  have := @is_compact.nonempty_Inter_of_directed_nonempty_compact_closed X _ X.clopen_cover _
    (λ I, is I) _ _ _ _,
  rcases this with ⟨x,hx⟩,
  refine ⟨x,λ I, _⟩,
  erw proj_fun_spec,
  apply hx,
  refine ⟨I,rfl⟩,
  { intros I J,
    dsimp,
    let K := I.common_refinement J,
    let f : K ≤ I := clopen_cover.common_refinement.le_left,
    let g : K ≤ J := clopen_cover.common_refinement.le_right,
    have hf := refines_spec f,
    have hg := refines_spec g,
    refine ⟨K, _, _⟩,
    erw ← compat _ _ f,
    apply hf,
    erw ← compat _ _ g,
    apply hg },
  { intros I, apply I.nonempty },
  { intros I,
    apply is_closed.compact,
    exact (I.clopen _).2 },
  { intros I,
    exact (I.clopen _).2 },
end

def cone (X : Profinite) : limits.cone (diagram : X.clopen_cover ⥤ _) := ⟨X,⟨proj⟩⟩

def limit_cone (X : Profinite) : limits.cone (diagram : X .clopen_cover ⥤ _) :=
lift_limit (Top.limit_cone_is_limit $ diagram ⋙ Profinite_to_Top)

def limit_cone_is_limit_cone (X : Profinite) : limits.is_limit X.limit_cone :=
lifted_limit_is_limit _

def limit_cone_iso (X : Profinite) :
  Profinite_to_Top.map_cone X.limit_cone ≅ Top.limit_cone _ := lifted_limit_maps_to_original _

lemma lift_injective : function.injective ((limit_cone_is_limit_cone _).lift X.cone) :=
begin
  suffices : function.injective
    ((Top.limit_cone_is_limit ((diagram : X.clopen_cover ⥤ _) ⋙ Profinite_to_Top)).lift
    (Profinite_to_Top.map_cone X.cone)), sorry,
  intros x y he,
  apply eq_of_proj_eq,
  intros I,
  apply_fun (Top.limit_cone _).π.app I at he,
  change ((Top.limit_cone_is_limit _).lift _ ≫ (Top.limit_cone _).π.app I) x =
    ((Top.limit_cone_is_limit _).lift _ ≫ (Top.limit_cone _).π.app I) y at he,
  simpa using he,
end

lemma lift_surjective : function.surjective ((limit_cone_is_limit_cone _).lift X.cone) :=
begin
  sorry,
  /-
  intros a,
  have := exists_of_compat (λ I, (limit_cone _).π.app I a) _,
  rcases a with ⟨a,ha⟩,
  rcases this with ⟨x,hx⟩,
  use x,
  ext1,
  ext1 I,
  dsimp [is_limit_limit_cone],
  apply hx,
  intros I J f,
  rcases a with ⟨a,ha⟩,
  dsimp [limit_cone],
  dsimp at ha,
  change (diagram.map (hom_of_le f)) (a I) = _,
  rw ha,
  -/
end

lemma lift_closed : is_closed_map ((limit_cone_is_limit_cone _).lift X.cone) :=
begin
  intros U hU,
  apply is_compact.is_closed,
  apply is_compact.image _ ((limit_cone_is_limit_cone _).lift X.cone).2,
  apply is_closed.compact hU,
end

def lift_equiv : X.cone.X ≃ (limit_cone X).X :=
equiv.of_bijective ((limit_cone_is_limit_cone _).lift X.cone) ⟨lift_injective , lift_surjective⟩

def lift_iso : X.cone.X ≅ (limit_cone X).X :=
{ hom := (limit_cone_is_limit_cone _).lift X.cone,
  inv :=
  { to_fun := lift_equiv.symm,
    continuous_to_fun := begin
      rw continuous_iff_is_closed,
      intros S hS,
      convert ← lift_closed S hS,
      erw equiv.image_eq_preimage lift_equiv,
    end },
  hom_inv_id' := begin
    ext1 x,
    change (lift_equiv.symm (lift_equiv x)) = x,
    simp,
  end,
  inv_hom_id' := begin
    ext1 x,
    change (lift_equiv (lift_equiv.symm x)) = x,
    simp,
  end }

lemma lift_iso_comm (I : X.clopen_cover) : lift_iso.hom ≫ (limit_cone _).π.app _ = proj I :=
by sorry

lemma lift_iso_inv (I : X.clopen_cover) : lift_iso.inv ≫ proj I = (limit_cone _).π.app _ :=
begin
  symmetry,
  rw iso.eq_inv_comp,
  apply lift_iso_comm,
end

def is_limit : is_limit X.cone :=
{ lift := λ S, (limit_cone_is_limit_cone _).lift S ≫ lift_iso.symm.hom,
  fac' := begin
    intros S j,
    erw [category.assoc, lift_iso_inv],
    simp,
  end,
  uniq' := begin
    intros S m h,
    erw iso.eq_comp_inv,
    ext1 x,
    sorry,
    --ext1,
    --ext1 j,
    --change (m ≫ X.cone.π.app j) x = _,
    --rw h,
    --refl,
  end }

end Profinite
