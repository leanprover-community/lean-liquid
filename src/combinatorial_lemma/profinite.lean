import combinatorial_lemma.profinite_setup

section

open category_theory
open category_theory.limits
open ProFiltPseuNormGrpWithTinv₁

open_locale nnreal big_operators

noncomputable theory

universe u

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

namespace lem98

variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' < 1)]
  (Λ : Type u) [polyhedral_lattice Λ] (S : Profinite.{u}) (N : ℕ) [hN : fact (0 < N)]

/-- `X ↦ X_{≤ c}`, (functorially in both `X` and `c`). -/
abbreviation lvl : ℝ≥0 ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' ⥤ Profinite.{u} :=
functor.flip $ to_PFPNG₁ _ ⋙ (ProFiltPseuNormGrp₁.level).flip

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
  ((lvl r').obj c).obj ((hom_functor.{u} r' Λ).obj ((Mbar.functor.{u u} r').obj S)) := rfl

/-- The cone with cone point `Hom(Λ, Mbar S)_{≤ c}` is indeed a limit cone. -/
def hom_Mbar_cone_is_limit (c) : is_limit (hom_Mbar_cone r' Λ S c) :=
is_limit_of_preserves _ $ limit.is_limit _

/-- the functor sending `T` to `T^n`. We use a custom `Profinite.product`
so we don't have to resort to `ulift (fin n)`. -/
def _root_.nat.fold_product (n : nat) :
  Profinite.{u} ⥤ Profinite.{u} :=
{ obj := λ T, Profinite.product (λ i : fin n, T),
  map := λ X Y f, Profinite.product.lift _ $ λ i, Profinite.product.π _ i ≫ f,
  map_id' := begin
    intros X,
    apply Profinite.product.hom_ext,
    simp,
  end,
  map_comp' := begin
    intros X Y Z f g,
    apply Profinite.product.hom_ext,
    simp,
  end }

example (T : Profinite.{u}) (n : nat) : Profinite := n.fold_product.obj T

-- Missing comphaus_filt_pseudo_normed_group.continuous_sum',
-- and comphaus_filt_pseudo_normed_group.sum'
def sum {c₁ c₂ : ℝ≥0} (n : nat) (h : ↑n * c₁ ≤ c₂) :
  (lvl r').obj c₁ ⋙ n.fold_product ⟶ (lvl r').obj c₂ :=
{ app := λ X,
  { to_fun := pseudo_normed_group.sum' n h,
    continuous_to_fun := comphaus_filtered_pseudo_normed_group.continuous_sum' _ _ },
  naturality' := begin
    intros  X Y f,
    ext,
    dsimp [nat.fold_product, ProFiltPseuNormGrp₁.level, to_PFPNG₁,
      Profinite.product.lift, Profinite.product.π, pseudo_normed_group.sum'],
    rw f.map_sum,
  end } .

-- A functorial version of `cast_le`.
def le {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) :
  (lvl r').obj c₁ ⟶ (lvl r').obj c₂ :=
{ app := λ X,
  { to_fun := pseudo_normed_group.cast_le' h,
    continuous_to_fun := begin
      haveI : fact (c₁ ≤ c₂) := ⟨h⟩,
      apply comphaus_filtered_pseudo_normed_group.continuous_cast_le,
    end },
  naturality' := λ A B f, by { ext, refl } }

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
