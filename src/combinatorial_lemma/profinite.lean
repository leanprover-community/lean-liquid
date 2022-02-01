import combinatorial_lemma.profinite_setup

section

open category_theory
open category_theory.limits
open ProFiltPseuNormGrpWithTinv₁

open_locale nnreal big_operators

noncomputable theory

universe u

variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' < 1)]
  (Λ : Type u) [polyhedral_lattice Λ] (S : Profinite.{u})

namespace pseudo_normed_group

def sum' {c₁ c₂ : ℝ≥0} {M : Type u} [pseudo_normed_group M]
  (n : ℕ) (h : ↑n * c₁ ≤ c₂) :
  (Π i : fin n, pseudo_normed_group.filtration M c₁) → pseudo_normed_group.filtration M c₂ :=
λ t, ⟨∑ i : fin n, (t i).1, begin
  apply filtration_mono,
  rotate 1,
  apply pseudo_normed_group.sum_mem_filtration,
  intros i hi, exact (t i).2,
  simpa,
end⟩

end pseudo_normed_group

namespace comphaus_filtered_pseudo_normed_group

lemma continuous_sum' {c₁ c₂ : ℝ≥0} {M : Type u} [comphaus_filtered_pseudo_normed_group M]
  (n : ℕ) (h : ↑n * c₁ ≤ c₂) :
  continuous (pseudo_normed_group.sum' n h :
    (Π (i : fin n), pseudo_normed_group.filtration M c₁) →
    pseudo_normed_group.filtration M c₂) := sorry

end comphaus_filtered_pseudo_normed_group

namespace Profinite

def pow (X : Profinite.{u}) (n : ℕ) : Profinite.{u} :=
Profinite.product (λ i : fin n, X)

def map_pow {X Y : Profinite.{u}} (f : X ⟶ Y) (n : ℕ) :
  X.pow n ⟶ Y.pow n :=
Profinite.product.lift _ $ λ n, Profinite.product.π _ n ≫ f

end Profinite

namespace ProFiltPseuNormGrpWithTinv₁

def level : ℝ≥0 ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' ⥤ Profinite.{u} :=
{ obj := λ c,
  { obj := λ X, Profinite.of $ pseudo_normed_group.filtration X c,
    map := λ X Y f, ⟨f.level _, f.continuous' _⟩,
    map_id' := sorry,
    map_comp' := sorry },
  map := λ c₁ c₂ h,
  { app := λ X, ⟨pseudo_normed_group.cast_le' h.le, begin
      haveI : fact (c₁ ≤ c₂) := ⟨h.le⟩,
      apply comphaus_filtered_pseudo_normed_group.continuous_cast_le,
    end ⟩,
    naturality' := sorry },
  map_id' := sorry,
  map_comp' := sorry }

instance (c) : preserves_limits ((level r').obj c) :=
begin
  change preserves_limits (to_PFPNG₁.{u} r' ⋙ ProFiltPseuNormGrp₁.level.obj.{u} c),
  apply_with limits.comp_preserves_limits { instances := ff },
  constructor, constructor, introsI J _, constructor,
  -- <-- looks like we have `preserves_limit` and not `preserves_limits`, but
  -- it should be trivial to add, if needed.
end

variable {r'}

abbreviation lvl (X : ProFiltPseuNormGrpWithTinv₁.{u} r') (c : ℝ≥0) : Profinite.{u} :=
((level r').obj c).obj X

abbreviation map_lvl {X Y : ProFiltPseuNormGrpWithTinv₁.{u} r'} (f : X ⟶ Y) (c : ℝ≥0) :
  X.lvl c ⟶ Y.lvl c := ((level r').obj c).map f

abbreviation cast_lvl {c₁ c₂ : ℝ≥0} (X : ProFiltPseuNormGrpWithTinv₁.{u} r') (h : c₁ ≤ c₂) :
  X.lvl c₁ ⟶ X.lvl c₂ := ((level r').map h.hom).app _

def sum {c₁ c₂ : ℝ≥0} (X : ProFiltPseuNormGrpWithTinv₁.{u} r') (n : ℕ) (h : ↑n * c₁ ≤ c₂) :
  (X.lvl c₁).pow n ⟶ X.lvl c₂ :=
⟨pseudo_normed_group.sum' _ h,
  comphaus_filtered_pseudo_normed_group.continuous_sum' _ _⟩

lemma le₁ (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) :
  ↑N * (c / ↑N + d) ≤ c + ↑N * d := sorry

lemma le₂ (N : ℕ) (c d : ℝ≥0) :
  c ≤ c + ↑N * d := le_self_add

/--
Given a `N : ℕ`, `c : ℝ≥0`, an `X : ProFiltPseuNormGrpWithTing₁ r'`, and a
  `t : Profinite.punit ⟶ X.lvl c`, this constructs the pullback of `t` along the projection
  `(X.lvl (c/N + d))^n ×_{X.lvl (c + N * d)} X.lvl c → X.lvl c`.
-/
def gadget (X : ProFiltPseuNormGrpWithTinv₁.{u} r')
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ X.lvl c) : Profinite.{u} :=
Profinite.pullback
(Profinite.pullback.snd (X.sum N (le₁ N c d)) (X.cast_lvl (le₂ N c d ))) t

def map_gadget {X Y : ProFiltPseuNormGrpWithTinv₁.{u} r'}
  (f : X ⟶ Y) (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ X.lvl c)
  (t' : Profinite.punit.{u} ⟶ Y.lvl c) (w : t ≫ map_lvl f c = t') :
  X.gadget N c d t ⟶ Y.gadget N c d t' :=
Profinite.pullback.lift _ _
(Profinite.pullback.fst _ _ ≫
  Profinite.pullback.lift _ _
  (Profinite.pullback.fst _ _ ≫
    Profinite.product.lift _ (λ i, Profinite.product.π _ i ≫ map_lvl f _))
  (Profinite.pullback.snd _ _ ≫ map_lvl f _) sorry)
(Profinite.pullback.snd _ _) sorry

def gadget_diagram {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c) :
  J ⥤ Profinite.{u} :=
{ obj := λ j, (K.obj j).gadget N c d (t ≫ map_lvl (C.π.app _) c),
  map := λ i j f, map_gadget (K.map f) _ _ _ _ _ sorry,
  map_id' := sorry,
  map_comp' := sorry }

def gadget_diagram_fst_snd {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c) :
  gadget_diagram C N c d t ⟶ K ⋙ (level r').obj c :=
{ app := λ j, Profinite.pullback.fst _ _ ≫ Profinite.pullback.snd _ _,
  naturality' := sorry }

def gadget_diagram_fst_fst {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c)
  (i : fin N) :
  gadget_diagram C N c d t ⟶ K ⋙ (level r').obj (c / ↑N + d) :=
{ app := λ j, Profinite.pullback.fst _ _ ≫ Profinite.pullback.fst _ _ ≫
    Profinite.product.π _ i,
  naturality' := sorry }

def gadget_cone {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c) :
  cone (gadget_diagram C N c d t) :=
{ X := C.X.gadget N c d t,
  π :=
  { app := λ j, map_gadget (C.π.app _) _ _ _ _ _ rfl,
    naturality' := sorry } }

def gadget_cone_is_limit {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (hC : ∀ a : ℝ≥0, is_limit (((level r').obj a).map_cone C))
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c) :
  is_limit (gadget_cone C N c d t) :=
{ lift := λ S,
    Profinite.pullback.lift _ _
      (Profinite.pullback.lift _ _
        (Profinite.product.lift _
          (λ i, (hC _).lift
            ((cones.postcompose (gadget_diagram_fst_fst C N c d t i)).obj S)))
        ((hC _).lift ((cones.postcompose (gadget_diagram_fst_snd C N c d t)).obj S)) sorry)
      (Profinite.punit.elim _) sorry,
  fac' := sorry,
  uniq' := sorry }

end ProFiltPseuNormGrpWithTinv₁

namespace lem98

open ProFiltPseuNormGrpWithTinv₁

instance (c : ℝ≥0) : preserves_limits (hom_functor.{u} r' Λ ⋙ (level r').obj c) :=
begin
  change preserves_limits (hom_functor r' Λ ⋙ to_PFPNG₁ r' ⋙ ProFiltPseuNormGrp₁.level.obj c),
  apply_instance,
end

def hom_diagram : discrete_quotient S ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' :=
S.fintype_diagram ⋙ Mbar.fintype_functor.{u u} r' ⋙ hom_functor r' Λ

/-- The cone over `hom_diagram` whose cone point is defeq to `Hom(Λ, Mbar S)`.
See lemma below. -/
def hom_Mbar_cone : cone (hom_diagram r' Λ S) :=
(hom_functor r' Λ).map_cone
  (limit.cone (S.fintype_diagram ⋙ Mbar.fintype_functor.{u u} r'))

@[simp]
lemma hom_Mbar_cone_X : (hom_Mbar_cone r' Λ S ).X =
  ((hom_functor.{u} r' Λ).obj ((Mbar.functor.{u u} r').obj S)) := rfl

/-- The cone with cone point `Hom(Λ, Mbar S)_{≤ c}` is indeed a limit cone. -/
def hom_Mbar_cone_is_limit (c) : is_limit (((level r').obj c).map_cone
  (hom_Mbar_cone r' Λ S)) :=
begin
  let E := (limit.cone (S.fintype_diagram ⋙ Mbar.fintype_functor.{u u} r')),
  change is_limit (((hom_functor.{u} r' Λ ⋙ (level r').obj c)).map_cone E),
  apply is_limit_of_preserves (hom_functor.{u} r' Λ ⋙ (level r').obj c)
    (limit.is_limit _),
  apply_instance,
end .

-- This should follow from the finite case of lem98.
lemma gadget_nonempty (N : ℕ) [fact (0 < N)] (T : discrete_quotient S)
  (c) (t) : nonempty ((gadget_diagram (hom_Mbar_cone r' Λ _) N c (d Λ N) t).obj T) :=
begin
  obtain ⟨h⟩ := lem98_finite Λ T N,
  specialize h c,
  let u : (hom_Mbar_cone r' Λ S).X ⟶ (hom_diagram r' Λ S).obj T :=
    ((hom_Mbar_cone r' Λ S).π.app T),
  let t' := t ≫ ((level r').obj c).map u,
  specialize h (t' punit.star).1 (t' punit.star).2,
  swap, apply_instance,
  obtain ⟨e,he1,he2⟩ := h,
  -- Now use `e`, `t'`, `he1` and `he2` to finish off the proof...
  sorry,
end

-- This should follow from Tychonoff and `gadget_nonempty`.
lemma key (N : ℕ) [fact (0 < N)] (c) (t) :
  nonempty (((hom_functor r' Λ).obj ((Mbar.functor.{u u} r').obj S)).gadget N c (d Λ N) t) :=
begin
  let E := gadget_cone (hom_Mbar_cone r' Λ _) N c (d Λ N) t,
  let hE : is_limit E := gadget_cone_is_limit _ _ _ _ _ _,
  swap, { intros a, apply hom_Mbar_cone_is_limit },
  let E' := Profinite.to_Top.map_cone E,
  let hE' : is_limit E' := is_limit_of_preserves _ hE,
  let G := gadget_diagram (hom_Mbar_cone r' Λ S) N c (d Λ N) t ⋙ Profinite.to_Top,
  let T : E'.X ≅ (Top.limit_cone G).X :=
    hE'.cone_point_unique_up_to_iso (Top.limit_cone_is_limit G),
  suffices : nonempty (Top.limit_cone G).X,
  { obtain ⟨a⟩ := this, exact ⟨T.inv a⟩, },
  apply_with Top.nonempty_limit_cone_of_compact_t2_cofiltered_system { instances := ff },
  { apply_instance },
  { intros, apply gadget_nonempty, },
  { intros j,
    change compact_space
      ((gadget_diagram (hom_Mbar_cone r' Λ S) N c (d Λ N) t).obj j),
    apply_instance },
  { intros j,
    change t2_space
      ((gadget_diagram (hom_Mbar_cone r' Λ S) N c (d Λ N) t).obj j),
    apply_instance },
end

theorem main (r' : ℝ≥0) [fact (0 < r')] [fact (r' < 1)]
  (Λ : Type u) [polyhedral_lattice Λ] (S : Profinite.{u}) (N : ℕ) [hN : fact (0 < N)] :
  pseudo_normed_group.splittable (Λ →+ (Mbar.functor.{u u} r').obj S) N (d Λ N) :=
begin
  constructor,
  intros c u hu,
  let t : Profinite.punit ⟶ ((hom_functor r' Λ).obj ((Mbar.functor.{u u} r').obj S)).lvl c :=
    Profinite.from_punit ⟨u,hu⟩,
  obtain ⟨K,hK⟩ := key r' Λ S N c t,
  rcases K with ⟨⟨⟨K₁,K₂⟩,hhK⟩,⟨⟩⟩,
  dsimp [t, Profinite.from_punit, Profinite.pullback.snd] at hK,
  dsimp at hhK,
  use (λ i, (K₁ i).1),
  split,
  { apply_fun (λ e, e.val) at hhK,
    change _ = K₂.val at hhK,
    apply_fun (λ e, e.val) at hK,
    rw hK at hhK,
    exact hhK.symm },
  { intros i,
    exact (K₁ i).2 }
end

end lem98

/-- Lemma 9.8 of [Analytic] -/
lemma lem98 (r' : ℝ≥0) [fact (0 < r')] [fact (r' < 1)]
  (Λ : Type*) [polyhedral_lattice Λ] (S : Profinite) (N : ℕ) [hN : fact (0 < N)] :
  pseudo_normed_group.splittable (Λ →+ (Mbar.functor r').obj S) N (lem98.d Λ N) :=
begin
  constructor,
  intros c x hx,
  -- This reduces to `lem98_finite`: See the first lines of the proof in [Analytic].
  sorry
end

end
