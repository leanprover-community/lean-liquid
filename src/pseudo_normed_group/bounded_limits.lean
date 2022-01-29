import pseudo_normed_group.category
import for_mathlib.ab_explicit_limits

open category_theory
open category_theory.limits

universe u
variables {J : Type u} [small_category J]

-- We can develop all this stuff for `CompHausFiltPseuNormGrp₁` as well, if needed.
namespace ProFiltPseuNormGrp₁

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

end ProFiltPseuNormGrp₁
