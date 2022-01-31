import pseudo_normed_group.category
import for_mathlib.ab_explicit_limits

import topology.category.Compactum

open category_theory
open category_theory.limits

universe u
variables {J : Type u} [small_category J]

structure PseuNormGrp₁ :=
(carrier : Type u)
[str : pseudo_normed_group carrier]
(exhaustive' : ∀ x : carrier, ∃ c : nnreal,
  x ∈ pseudo_normed_group.filtration carrier c)

namespace PseuNormGrp₁

instance : has_coe_to_sort PseuNormGrp₁.{u} (Type u) := ⟨carrier⟩
instance (M : PseuNormGrp₁.{u}) : pseudo_normed_group M := M.str

lemma exhaustive (M : PseuNormGrp₁) (x : M) :
  ∃ c, x ∈ pseudo_normed_group.filtration M c := M.exhaustive' x

instance : category PseuNormGrp₁.{u} :=
{ hom := λ A B, strict_pseudo_normed_group_hom A B,
  id := λ A, strict_pseudo_normed_group_hom.id A,
  comp := λ A B C f g, f.comp g }

@[simp]
lemma id_apply (M : PseuNormGrp₁) (x : M) : (𝟙 M : M ⟶ M) x = x := rfl

@[simp]
lemma comp_apply {A B C : PseuNormGrp₁} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
  (f ≫ g) a = g (f a) := rfl

def to_Ab : PseuNormGrp₁.{u} ⥤ Ab.{u} :=
{ obj := λ M, AddCommGroup.of M,
  map := λ M N f, f.to_add_monoid_hom }

variable {K : J ⥤ PseuNormGrp₁.{u}}
variable (C : limits.limit_cone (K ⋙ to_Ab))

def bounded_elements : add_subgroup C.cone.X :=
{ carrier := { x | ∃ c, ∀ j, C.cone.π.app j x ∈ pseudo_normed_group.filtration (K.obj j) c },
  zero_mem' := ⟨0, λ j, by { simp, apply pseudo_normed_group.zero_mem_filtration } ⟩,
  add_mem' := λ a b ha hb, begin
    obtain ⟨c,hc⟩ := ha,
    obtain ⟨d,hd⟩ := hb,
    use c + d,
    intros j,
    simp,
    apply pseudo_normed_group.add_mem_filtration,
    apply hc,
    apply hd,
  end,
  neg_mem' := λ a ha, begin
    obtain ⟨c,hc⟩ := ha,
    use c,
    intros j,
    simp,
    apply pseudo_normed_group.neg_mem_filtration,
    apply hc,
  end }

def bounded_elements.filt (c : nnreal) : set C.cone.X :=
{ x | ∀ j, C.cone.π.app j x ∈ pseudo_normed_group.filtration (K.obj j) c }

def bounded_elements.filt_incl (c : nnreal) :
  bounded_elements.filt C c → bounded_elements C :=
λ x, ⟨x, c, x.2⟩

def bounded_elements.filtration (c : nnreal) : set (bounded_elements C) :=
set.range (bounded_elements.filt_incl _ c)

def bounded_cone_point : PseuNormGrp₁ :=
{ carrier := bounded_elements C,
  str :=
  { filtration := bounded_elements.filtration _,
    filtration_mono := begin
      intros c₁ c₂ h x hx,
      obtain ⟨t,rfl⟩ := hx, refine ⟨⟨t,_⟩,rfl⟩, intros i,
      apply pseudo_normed_group.filtration_mono h, apply t.2,
    end,
    zero_mem_filtration := begin
      intros c, refine ⟨⟨0,λ i, _⟩,rfl⟩, simp,
        apply pseudo_normed_group.zero_mem_filtration
    end,
    neg_mem_filtration := begin
      intros c x hx,
      obtain ⟨t,rfl⟩ := hx, refine ⟨⟨-t, λ i, _⟩, rfl⟩, simp,
      apply pseudo_normed_group.neg_mem_filtration, apply t.2
    end,
    add_mem_filtration := begin
      intros c₁ c₂ x₁ x₂ h₁ h₂,
      obtain ⟨t₁,rfl⟩ := h₁, obtain ⟨t₂,rfl⟩ := h₂,
      refine ⟨⟨t₁ + t₂, λ i, _⟩, rfl⟩, simp,
      apply pseudo_normed_group.add_mem_filtration, apply t₁.2, apply t₂.2,
    end },
    exhaustive' := begin
      intros m,
      obtain ⟨c,hc⟩ := m.2,
      refine ⟨c,⟨m.1, hc⟩, by { ext, refl }⟩,
    end }

def bounded_cone : cone K :=
{ X := bounded_cone_point C,
  π :=
  { app := λ j,
    { to_fun := λ x, C.cone.π.app _ x.1,
      map_zero' := by simp,
      map_add' := λ x y, by simp,
      strict' := begin
        rintros c x ⟨x,rfl⟩,
        apply x.2,
      end },
    naturality' := begin
      intros i j f,
      ext,
      dsimp,
      rw ← C.cone.w f,
      refl,
    end } }

def bounded_cone_lift (S : cone K) : S.X ⟶ bounded_cone_point C :=
{ to_fun := λ x, ⟨C.2.lift (to_Ab.map_cone S) x, begin
    obtain ⟨c,hc⟩ := S.X.exhaustive x,
    use c,
    intros j,
    rw [← Ab.comp_apply, C.2.fac],
    apply (S.π.app j).strict,
    exact hc,
  end⟩,
  map_zero' := by { ext, simp },
  map_add' := λ x y, by { ext, simp },
  strict' := begin
    intros c x hx,
    refine ⟨⟨_, λ j, _⟩,rfl⟩,
    erw [← Ab.comp_apply, C.2.fac],
    apply (S.π.app j).strict,
    exact hx,
  end }

def bounded_cone_is_limit : is_limit (bounded_cone C) :=
{ lift := λ S, bounded_cone_lift C S,
  fac' := begin
    intros S j,
    ext,
    dsimp [bounded_cone_lift, bounded_cone],
    rw [← Ab.comp_apply, C.2.fac],
    refl,
  end,
  uniq' := begin
    intros S m hm,
    ext,
    dsimp [bounded_cone_lift, bounded_cone],
    apply Ab.is_limit_ext,
    intros j,
    rw [← Ab.comp_apply, C.2.fac],
    dsimp,
    rw ← hm,
    refl,
  end }

instance : has_limits PseuNormGrp₁ :=
begin
  constructor, introsI J hJ, constructor, intros K,
  exact has_limit.mk ⟨_, bounded_cone_is_limit ⟨_,limit.is_limit _⟩⟩,
end

open pseudo_normed_group

lemma mem_filtration_iff_of_is_limit (C : cone K) (hC : is_limit C)
  (x : C.X) (c : nnreal) :
  x ∈ pseudo_normed_group.filtration C.X c ↔
  (∀ j : J, C.π.app j x ∈ pseudo_normed_group.filtration (K.obj j) c) :=
begin
  split,
  { intros h j,
    exact (C.π.app j).strict h },
  { intros h,
    let E := bounded_cone ⟨_, Ab.explicit_limit_cone_is_limit _⟩,
    let e : C ≅ E := hC.unique_up_to_iso (bounded_cone_is_limit _),
    let eX : C.X ≅ E.X := (cones.forget _).map_iso e,
    let w := eX.hom x,
    have hw : ∀ j, E.π.app j w ∈ filtration (K.obj j) c,
    { intros j,
      dsimp only [w],
      change (eX.hom ≫ E.π.app _) _ ∈ _,
      dsimp only [eX, functor.map_iso, cones.forget],
      convert h j,
      simp },
    suffices : w ∈ filtration E.X c,
    { convert eX.inv.strict this,
      change _ = (eX.hom ≫ eX.inv) x,
      rw iso.hom_inv_id,
      refl },
    refine ⟨⟨_,hw⟩,rfl⟩ }
end

@[simps]
def _root_.strict_pseudo_normed_group_hom.level {M N : Type*}
  [pseudo_normed_group M] [pseudo_normed_group N]
  (f : strict_pseudo_normed_group_hom M N) (c) :
  filtration M c → filtration N c :=
λ x, ⟨f x, f.strict x.2⟩

@[simp]
lemma _root_.strict_pseudo_normed_group_hom.level_id
  (M : Type*) [pseudo_normed_group M] (c) :
  (strict_pseudo_normed_group_hom.id M).level c = id := by { ext, refl }

@[simp]
def _root_.strict_pseudo_normed_group_hom.level_comp {M N L : Type*}
  [pseudo_normed_group M] [pseudo_normed_group N] [pseudo_normed_group L]
  (f : strict_pseudo_normed_group_hom M N) (g : strict_pseudo_normed_group_hom N L) (c) :
  (f.comp g).level c = g.level c ∘ f.level c := by { ext, refl }

@[simps]
def level : nnreal ⥤ PseuNormGrp₁.{u} ⥤ Type u :=
{ obj := λ c,
  { obj := λ M, filtration M c,
    map := λ X Y f, f.level _,
    map_id' := λ M, strict_pseudo_normed_group_hom.level_id M _,
    map_comp' := λ M N L f g, f.level_comp g c },
  map := λ c₁ c₂ h,
  { app := λ M, pseudo_normed_group.cast_le' h.le } } .

def level_cone_iso_hom (c) (t : (level.obj c).obj (bounded_cone_point C)) :
  (K ⋙ level.obj c).sections :=
{ val := λ j,
  { val := C.cone.π.app j t.1.1,
    property := begin
      obtain ⟨w,hw⟩ := t.2,
      apply_fun (λ e, e.val) at hw,
      rw ← hw,
      apply w.2
    end },
  property := begin
    intros i j f,
    ext,
    dsimp,
    rw ← C.cone.w f,
    refl,
  end }

def level_cone_iso_inv (c) (t : (K ⋙ level.obj c).sections) :
  (level.obj c).obj (bounded_cone_point C) :=
{ val :=
  { val := C.2.lift (Ab.explicit_limit_cone _) ⟨λ j, (t.1 j).1, begin
      intros i j f,
      dsimp,
      change _ = (t.val _).val,
      rw ← t.2 f,
      refl,
    end⟩,
    property := begin
      use c,
      intros j,
      rw [← Ab.comp_apply, C.2.fac],
      dsimp [Ab.explicit_limit_cone],
      apply (t.1 j).2,
    end },
  property := begin
    refine ⟨⟨_,_⟩,rfl⟩,
    intros j,
    dsimp,
    rw [← Ab.comp_apply, C.2.fac],
    dsimp [Ab.explicit_limit_cone],
    apply (t.1 j).2,
  end } .

def level_cone_iso (c) :
  (level.obj c).map_cone (bounded_cone C) ≅ types.limit_cone _ :=
cones.ext
{ hom := level_cone_iso_hom _ _,
  inv := level_cone_iso_inv _ _,
  hom_inv_id' := begin
    ext,
    dsimp [level_cone_iso_inv, level_cone_iso_hom],
    apply Ab.is_limit_ext,
    intros j,
    rw [← Ab.comp_apply, C.2.fac],
    refl,
  end,
  inv_hom_id' := begin
    ext,
    dsimp [level_cone_iso_inv, level_cone_iso_hom],
    rw [← Ab.comp_apply, C.2.fac],
    refl,
  end }
begin
  intros j,
  ext,
  refl,
end

instance (c) : preserves_limits (level.obj c) :=
begin
  constructor, introsI J hJ, constructor, intros K,
  apply preserves_limit_of_preserves_limit_cone
    (bounded_cone_is_limit ⟨_, Ab.explicit_limit_cone_is_limit _⟩),
  apply is_limit.of_iso_limit (types.limit_cone_is_limit _) (level_cone_iso _ _).symm,
end

end PseuNormGrp₁

-- We can develop all this stuff for `CompHausFiltPseuNormGrp₁` as well, if needed.
namespace ProFiltPseuNormGrp₁

@[simp]
lemma id_apply {A : ProFiltPseuNormGrp₁} (a : A) : (𝟙 A : A ⟶ A) a = a := rfl

@[simp]
lemma comp_apply {A B C : ProFiltPseuNormGrp₁} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
  (f ≫ g) a = g (f a) := rfl

def to_PNG₁ :
  ProFiltPseuNormGrp₁.{u} ⥤ PseuNormGrp₁.{u} :=
{ obj := λ M,
  { carrier := M,
    exhaustive' := M.exhaustive },
  map := λ X Y f, { strict' := λ c x h, f.strict h .. f.to_add_monoid_hom } }

variable (K : J ⥤ ProFiltPseuNormGrp₁.{u})

def to_PNG₁_level (c) :
  to_PNG₁ ⋙ PseuNormGrp₁.level.obj c ≅ level.obj c ⋙ forget _ :=
nat_iso.of_components (λ x, iso.refl _) $ by tidy

lemma level_eq_level_map {A B : PseuNormGrp₁} (f : A ⟶ B)
  (c : nnreal) : (PseuNormGrp₁.level.obj c).map f =
  pseudo_normed_group.level f (λ a b c, f.strict c) c := rfl

instance {J : Type u} (c : nnreal)
  [small_category J]
  (K : J ⥤ ProFiltPseuNormGrp₁)
  (S : cone K) : topological_space ((PseuNormGrp₁.level.obj c).obj (to_PNG₁.map_cone S).X) :=
begin
  change topological_space ((level.obj c).obj S.X),
  apply_instance
end

lemma to_PNG₁_lift_is_limit_continuous_aux {J : Type u} (c : nnreal)
  [small_category J]
  (K : J ⥤ ProFiltPseuNormGrp₁.{u})
  {C : cone K}
  (hC : is_limit (to_PNG₁.map_cone C))
  (S : cone K) :
  continuous
    ((PseuNormGrp₁.level.obj c).map (hC.lift (to_PNG₁.map_cone S))) :=
begin
  let C₁ : cone ((K ⋙ to_PNG₁) ⋙ PseuNormGrp₁.level.obj c):=
      (PseuNormGrp₁.level.obj c).map_cone (to_PNG₁.map_cone C),
  let hC₁ : is_limit C₁ := is_limit_of_preserves (PseuNormGrp₁.level.obj c) hC,
  let η : (K ⋙ to_PNG₁) ⋙ PseuNormGrp₁.level.obj c ≅
    (K ⋙ level.obj c) ⋙ forget _ := iso_whisker_left K (to_PNG₁_level c),
  let C₂ : cone ((K ⋙ level.obj c) ⋙ forget _) :=
    (forget _).map_cone ((level.obj c).map_cone C),
  let hC₂ : is_limit C₂ := (is_limit.postcompose_hom_equiv η _).symm hC₁,
  let C₃ : cone (K ⋙ level.obj c) := (level.obj c).map_cone C,
  let hC₃ : is_limit C₃ := is_limit_of_reflects (forget _) hC₂,
  have : (PseuNormGrp₁.level.obj c).map (hC.lift (to_PNG₁.map_cone S)) =
    (forget _).map (hC₃.lift ((level.obj c).map_cone S)),
  { have : (PseuNormGrp₁.level.obj c).map (hC.lift (to_PNG₁.map_cone S)) =
      hC₁.lift ((PseuNormGrp₁.level.obj c).map_cone (to_PNG₁.map_cone S)),
    { apply hC₁.uniq ((PseuNormGrp₁.level.obj c).map_cone (to_PNG₁.map_cone S)),
      intros j,
      dsimp,
      simp only [← functor.map_comp],
      congr' 1,
      erw hC.fac,
      refl },
    rw this,
    symmetry,
    apply (hC₁.uniq ((PseuNormGrp₁.level.obj c).map_cone (to_PNG₁.map_cone S))),
    intros j,
    have : (forget Profinite).map (hC₃.lift ((level.obj c).map_cone S)) =
      hC₂.lift ((forget _).map_cone (((level.obj c).map_cone S))),
    { apply  hC₂.uniq ((forget Profinite).map_cone ((level.obj c).map_cone S)),
      intros j,
      dsimp,
      change (forget _).map _ ≫ (forget _).map _ = (forget _).map _,
      simp only [← functor.map_comp],
      congr' 1,
      erw hC₃.fac,
      refl },
    rw this, clear this,
    erw hC₂.fac,
    refl },
  rw this,
  change continuous (hC₃.lift ((level.obj c).map_cone S)),
  continuity
end

def to_PNG₁_lift_is_limit {C : cone K} (hC : is_limit (to_PNG₁.map_cone C)) : is_limit C :=
{ lift := λ S,
  { continuous' := λ c, begin
      dsimp,
      erw ← level_eq_level_map,
      apply to_PNG₁_lift_is_limit_continuous_aux,
    end,
    ..(hC.lift (to_PNG₁.map_cone S)) },
  fac' := begin
    intros S j,
    ext,
    dsimp,
    have := hC.fac (to_PNG₁.map_cone S) j,
    apply_fun (λ e, e x) at this,
    exact this,
  end,
  uniq' := begin
    intros S m hm,
    dsimp,
    have : to_PNG₁.map m = hC.lift (to_PNG₁.map_cone S),
    { apply hC.uniq (to_PNG₁.map_cone S),
      intros j,
      ext x,
      specialize hm j,
      apply_fun (λ e, e x) at hm,
      exact hm },
    ext x,
    change (to_PNG₁.map m) x = _,
    rw this,
    refl,
  end }

namespace liftable_cone_of_is_limit_aux

variable (C : limits.limit_cone (K ⋙ to_PNG₁))
include C

instance (c : nnreal) :
  topological_space (pseudo_normed_group.filtration C.cone.X c) := sorry

instance (c : nnreal) :
  t2_space (pseudo_normed_group.filtration C.cone.X c) := sorry

instance (c : nnreal) :
  compact_space (pseudo_normed_group.filtration C.cone.X c) := sorry

instance (c : nnreal) :
  totally_disconnected_space (pseudo_normed_group.filtration C.cone.X c) := sorry

def π_level (c) (j) : pseudo_normed_group.filtration C.cone.X c →
  pseudo_normed_group.filtration (K.obj j) c :=
pseudo_normed_group.level (C.cone.π.app j) (C.cone.π.app j).strict _

lemma continuous_π_level (c) (j) : continuous (π_level K C c j) := sorry

instance : profinitely_filtered_pseudo_normed_group C.cone.X :=
{ continuous_add' := sorry,
  continuous_neg' := sorry,
  continuous_cast_le := sorry,
  ..(infer_instance : pseudo_normed_group C.cone.X) }

def lifted_cone : cone K :=
{ X :=
  { M := C.cone.X,
    exhaustive' := C.cone.X.exhaustive },
  π :=
  { app := λ j,
    { continuous' := λ c, continuous_π_level K C c j,
      ..(C.cone.π.app j)},
    naturality' := begin
      intros i j f,
      ext,
      dsimp,
      rw ← (C.cone.w f),
      refl,
    end } }

def valid_lift : to_PNG₁.map_cone (lifted_cone K C) ≅ C.cone :=
cones.ext
{ hom :=
  { to_fun := id,
    map_zero' := rfl,
    map_add' := λ _ _, rfl,
    strict' := λ _ _ h, h },
  inv :=
  { to_fun := id,
    map_zero' := rfl,
    map_add' := λ _ _, rfl,
    strict' := λ _ _ h, h } } $ by tidy

end liftable_cone_of_is_limit_aux

def liftable_cone_of_is_limit (C : cone (K ⋙ to_PNG₁)) (hC : is_limit C) :
  liftable_cone K to_PNG₁ C :=
{ lifted_cone := liftable_cone_of_is_limit_aux.lifted_cone _ ⟨_,hC⟩,
  valid_lift := liftable_cone_of_is_limit_aux.valid_lift _ _ }

instance : creates_limit K to_PNG₁ :=
{ reflects := λ C, to_PNG₁_lift_is_limit _,
  lifts := λ c hc, liftable_cone_of_is_limit _ _ hc }

instance : creates_limits to_PNG₁ :=
{ creates_limits_of_shape := by { introsI J _, constructor, } }

/-
@[simp]
lemma id_apply {A : ProFiltPseuNormGrp₁} (a : A) : (𝟙 A : A ⟶ A) a = a := rfl

@[simp]
lemma comp_apply {A B C : ProFiltPseuNormGrp₁} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
  (f ≫ g) a = g (f a) := rfl

attribute [simps] level Ab.explicit_limit_cone

def to_Ab : ProFiltPseuNormGrp₁.{u} ⥤ Ab.{u} :=
{ obj := λ M, AddCommGroup.of M,
  map := λ M N f, f.to_add_monoid_hom }

variable {K : J ⥤ ProFiltPseuNormGrp₁.{u}}
variable (C : limits.limit_cone (K ⋙ to_Ab))

def bounded_elements : add_subgroup C.cone.X :=
{ carrier := { x | ∃ c, ∀ j, C.cone.π.app j x ∈ pseudo_normed_group.filtration (K.obj j) c },
  zero_mem' := ⟨0, λ j, by { simp, apply pseudo_normed_group.zero_mem_filtration } ⟩,
  add_mem' := λ a b ha hb, begin
    obtain ⟨c,hc⟩ := ha,
    obtain ⟨d,hd⟩ := hb,
    use c + d,
    intros j,
    simp,
    apply pseudo_normed_group.add_mem_filtration,
    apply hc,
    apply hd,
  end,
  neg_mem' := λ a ha, begin
    obtain ⟨c,hc⟩ := ha,
    use c,
    intros j,
    simp,
    apply pseudo_normed_group.neg_mem_filtration,
    apply hc,
  end }

def bounded_elements.filt (c : nnreal) : set C.cone.X :=
{ x | ∀ j, C.cone.π.app j x ∈ pseudo_normed_group.filtration (K.obj j) c }

def bounded_elements.filt_incl (c : nnreal) :
  bounded_elements.filt C c → bounded_elements C :=
λ x, ⟨x, c, x.2⟩

def bounded_elements.filtration (c : nnreal) : set (bounded_elements C) :=
set.range (bounded_elements.filt_incl _ c)

@[simps]
def bounded_elements.filtration_to_Profinite_limit_cone (c : nnreal) :
  bounded_elements.filtration C c → (Profinite.limit_cone (K ⋙ level.obj c)).X :=
λ t, ⟨λ j, ⟨C.cone.π.app _ t.1.1, by { rcases t with ⟨_,w,rfl⟩, apply w.2}⟩,
    by { intros i j f, ext, dsimp, rw ← C.cone.w f, refl }⟩

@[simps]
def bounded_elements.Profinite_limit_cone_to_filtration (c : nnreal) :
(Profinite.limit_cone (K ⋙ level.obj c)).X → bounded_elements.filtration C c := λ t,
{ val := ⟨C.2.lift (Ab.explicit_limit_cone _) ⟨λ j, (t.1 j).1,
  by { intros i j f, dsimp, change _ = (t.val _).val, rw ← t.2 f, refl }⟩,
  by { use c, intros j, dsimp, rw [← Ab.comp_apply, C.2.fac], exact (t.1 j).2 }⟩,
  property := by { refine ⟨⟨C.2.lift (Ab.explicit_limit_cone _) ⟨λ j, (t.1 j).1,
    by { intros i j f, dsimp, change _ = (t.val _).val, rw ← t.2 f, refl }⟩, _⟩, _⟩,
    { intros j, rw [← Ab.comp_apply, C.2.fac], exact (t.1 j).2 },
    { ext, refl } } }

def bounded_elements.filtration_equiv (c : nnreal) :
  bounded_elements.filtration C c ≃ (Profinite.limit_cone (K ⋙ level.obj c)).X :=
{ to_fun := bounded_elements.filtration_to_Profinite_limit_cone C c,
  inv_fun := bounded_elements.Profinite_limit_cone_to_filtration C c,
  left_inv := by { rintros ⟨⟨f,h2⟩,h3⟩, ext, dsimp, apply Ab.is_limit_ext,
    intros j, rw [← Ab.comp_apply, C.2.fac], refl },
  right_inv := by { rintros ⟨f,hf⟩, ext, dsimp, rw [← Ab.comp_apply, C.2.fac], refl } }

instance (c : nnreal) :
  topological_space (bounded_elements.filtration C c) :=
topological_space.induced (bounded_elements.filtration_equiv C c) infer_instance

instance (c : nnreal) :
  t2_space (bounded_elements.filtration C c) := sorry

instance (c : nnreal) :
  compact_space (bounded_elements.filtration C c) := sorry

instance (c : nnreal) :
  totally_disconnected_space (bounded_elements.filtration C c) := sorry

def bounded_cone_point : ProFiltPseuNormGrp₁ :=
{ M := bounded_elements C,
  str :=
  { filtration := bounded_elements.filtration _,
    filtration_mono := begin
      intros c₁ c₂ h x hx,
      obtain ⟨t,rfl⟩ := hx, refine ⟨⟨t,_⟩,rfl⟩, intros i,
      apply pseudo_normed_group.filtration_mono h, apply t.2,
    end,
    zero_mem_filtration := begin
      intros c, refine ⟨⟨0,λ i, _⟩,rfl⟩, simp,
        apply pseudo_normed_group.zero_mem_filtration
    end,
    neg_mem_filtration := begin
      intros c x hx,
      obtain ⟨t,rfl⟩ := hx, refine ⟨⟨-t, λ i, _⟩, rfl⟩, simp,
      apply pseudo_normed_group.neg_mem_filtration, apply t.2
    end,
    add_mem_filtration := begin
      intros c₁ c₂ x₁ x₂ h₁ h₂,
      obtain ⟨t₁,rfl⟩ := h₁, obtain ⟨t₂,rfl⟩ := h₂,
      refine ⟨⟨t₁ + t₂, λ i, _⟩, rfl⟩, simp,
      apply pseudo_normed_group.add_mem_filtration, apply t₁.2, apply t₂.2,
    end,
    continuous_add' := sorry,
    continuous_neg' := sorry,
    continuous_cast_le := sorry },
    exhaustive' := begin
      intros m,
      obtain ⟨c,hc⟩ := m.2,
      refine ⟨c,⟨m.1, hc⟩, by { ext, refl }⟩,
    end }

def bounded_cone : cone K :=
{ X := bounded_cone_point C,
  π :=
  { app := λ j,
    { to_fun := λ x, C.cone.π.app _ x.1,
      map_zero' := by simp,
      map_add' := λ x y, by simp,
      strict' := begin
        rintros c x ⟨x,rfl⟩,
        apply x.2,
      end,
      continuous' := sorry },
    naturality' := begin
      intros i j f,
      ext,
      dsimp,
      rw ← C.cone.w f,
      refl,
    end } }

def bounded_cone_lift (S : cone K) : S.X ⟶ bounded_cone_point C :=
{ to_fun := λ x, ⟨C.2.lift (to_Ab.map_cone S) x, begin
    obtain ⟨c,hc⟩ := S.X.exhaustive x,
    use c,
    intros j,
    rw [← Ab.comp_apply, C.2.fac],
    apply (S.π.app j).strict,
    exact hc,
  end⟩,
  map_zero' := by { ext, simp },
  map_add' := λ x y, by { ext, simp },
  strict' := begin
    intros c x hx,
    refine ⟨⟨_, λ j, _⟩,rfl⟩,
    erw [← Ab.comp_apply, C.2.fac],
    apply (S.π.app j).strict,
    exact hx,
  end,
  continuous' := sorry }

def bounded_cone_is_limit : is_limit (bounded_cone C) :=
{ lift := λ S, bounded_cone_lift C S,
  fac' := begin
    intros S j,
    ext,
    dsimp [bounded_cone_lift, bounded_cone],
    rw [← Ab.comp_apply, C.2.fac],
    refl,
  end,
  uniq' := begin
    intros S m hm,
    ext,
    dsimp [bounded_cone_lift, bounded_cone],
    apply Ab.is_limit_ext,
    intros j,
    rw [← Ab.comp_apply, C.2.fac],
    dsimp,
    rw ← hm,
    refl,
  end }

-/
end ProFiltPseuNormGrp₁
