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

def gadget_cone {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K)
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c) :
  cone (gadget_diagram C N c d t) :=
{ X := C.X.gadget N c d t,
  π :=
  { app := λ j, map_gadget (C.π.app _) _ _ _ _ _ rfl,
    naturality' := sorry } }

def gadget_cone_is_limit {J : Type u} [small_category J]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r'} (C : cone K) (hC : is_limit C)
  (N : ℕ) [fact (0 < N)] (c d : ℝ≥0) (t : Profinite.punit.{u} ⟶ C.X.lvl c) :
  is_limit (gadget_cone C N c d t) :=
{ lift := λ S, sorry,
  fac' := sorry,
  uniq' := sorry }

end ProFiltPseuNormGrpWithTinv₁

namespace lem98

open ProFiltPseuNormGrpWithTinv₁

/-- The functor sending a discrerte quotient of `S`, say `T`, to `Hom(Λ,Mbar T)_{≤ c}`. -/
def hom_diagram (c : nnreal) : discrete_quotient S ⥤ Profinite :=
S.fintype_diagram ⋙ Mbar.fintype_functor.{u u} r' ⋙ hom_functor r' Λ ⋙
  to_PFPNG₁ r' ⋙ ProFiltPseuNormGrp₁.level.obj c

/-- The cone over `hom_diagram` whose cone point is defeq to `Hom(Λ, Mbar S)_{≤ c}`.
See lemma below. -/
def hom_Mbar_cone (c) : cone (hom_diagram r' Λ S c) :=
(hom_functor r' Λ ⋙ to_PFPNG₁ r' ⋙ ProFiltPseuNormGrp₁.level.obj c).map_cone
  (limit.cone (S.fintype_diagram ⋙ Mbar.fintype_functor.{u u} r'))

@[simp]
lemma hom_Mbar_cone_X (c) : (hom_Mbar_cone r' Λ S c).X =
  ((hom_functor.{u} r' Λ).obj ((Mbar.functor.{u u} r').obj S)).lvl c := rfl

/-- The cone with cone point `Hom(Λ, Mbar S)_{≤ c}` is indeed a limit cone. -/
def hom_Mbar_cone_is_limit (c) : is_limit (hom_Mbar_cone r' Λ S c) :=
is_limit_of_preserves _ $ limit.is_limit _

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
