import category_theory.abelian.projective
import pseudo_normed_group.category

import condensed.basic

/-!
# Properties of the category of condensed abelian groups

-/

open category_theory category_theory.limits

universes v u

namespace Condensed

instance : preadditive (Condensed Ab.{u+1}) := sorry

instance : abelian (Condensed Ab.{u+1}) := sorry

instance : enough_projectives (Condensed Ab.{u+1}) := sorry

end Condensed

namespace CompHausFiltPseuNormGrp₁

open_locale nnreal
open pseudo_normed_group comphaus_filtered_pseudo_normed_group

def presheaf (A : CompHausFiltPseuNormGrp₁) (S : Profinite) : Type* :=
{ f : S → A // ∃ (c : ℝ≥0) (f₀ : S → filtration A c), continuous f₀ ∧ f = coe ∘ f₀ }

namespace presheaf

variables (A : CompHausFiltPseuNormGrp₁) (S : Profinite)

@[ext]
lemma ext {A : CompHausFiltPseuNormGrp₁} {S : Profinite} (f g : presheaf A S) : f.1 = g.1 → f = g :=
subtype.ext

instance : has_zero (presheaf A S) := ⟨⟨0, 0, 0, continuous_zero, rfl⟩⟩

instance : has_neg (presheaf A S) :=
⟨λ f, ⟨-f.1,
  begin
    obtain ⟨_, c, f, hf, rfl⟩ := f,
    refine ⟨c, λ s, - f s, _, rfl⟩,
    exact (continuous_neg' c).comp hf
  end⟩⟩

instance : has_add (presheaf A S) :=
⟨λ f g, ⟨f.1 + g.1,
  begin
    obtain ⟨_, cf, f, hf, rfl⟩ := f,
    obtain ⟨_, cg, g, hg, rfl⟩ := g,
    refine ⟨cf + cg, λ s, ⟨f s + g s, add_mem_filtration (f s).2 (g s).2⟩, _, rfl⟩,
    have aux := (hf.prod_mk hg),
    exact (continuous_add' cf cg).comp aux,
  end⟩⟩

instance : has_sub (presheaf A S) :=
⟨λ f g, ⟨f.1 - g.1,
  begin
    obtain ⟨_, cf, f, hf, rfl⟩ := f,
    obtain ⟨_, cg, g, hg, rfl⟩ := g,
    refine ⟨cf + cg, λ s, ⟨f s - g s, sub_mem_filtration (f s).2 (g s).2⟩, _, rfl⟩,
    have aux := (hf.prod_mk ((continuous_neg' cg).comp hg)),
    simp only [sub_eq_add_neg],
    exact (continuous_add' cf cg).comp aux,
  end⟩⟩

variables {A S}

protected def nsmul (n : ℕ) (f : presheaf A S) : presheaf A S :=
⟨n • f.1,
begin
  obtain ⟨_, c, f, hf, rfl⟩ := f,
  refine ⟨n * c, λ s, ⟨n • f s, nat_smul_mem_filtration _ _ _ (f s).2⟩, _, rfl⟩,
  sorry
end⟩

protected def gsmul (n : ℤ) (f : presheaf A S) : presheaf A S :=
⟨n • f.1,
begin
  obtain ⟨_, c, f, hf, rfl⟩ := f,
  refine ⟨n.nat_abs * c, λ s, ⟨n • f s, int_smul_mem_filtration _ _ _ (f s).2⟩, _, rfl⟩,
  sorry
end⟩

variables (A S)

instance : add_comm_group (presheaf A S) :=
{ zero := 0,
  add := (+),
  nsmul := presheaf.nsmul,
  gsmul := presheaf.gsmul,
  add_assoc := sorry,
  zero_add := sorry,
  add_zero := sorry,
  add_comm := sorry,
  add_left_neg := sorry,
  sub_eq_add_neg := sorry,
  nsmul_zero' := sorry,
  nsmul_succ' := sorry,
  gsmul_zero' := sorry,
  gsmul_succ' := sorry,
  gsmul_neg' := sorry,
  .. presheaf.has_sub A S, .. presheaf.has_neg A S }

def comap (A : CompHausFiltPseuNormGrp₁) {S T : Profinite} (φ : S ⟶ T) :
  presheaf A T →+ presheaf A S :=
{ to_fun := λ f, ⟨f.1 ∘ φ,
  begin
    obtain ⟨_, c, f, hf, rfl⟩ := f,
    refine ⟨c, f ∘ φ, hf.comp φ.continuous, rfl⟩,
  end⟩,
  map_zero' := rfl,
  map_add' := by { intros, refl } }

def map {A B : CompHausFiltPseuNormGrp₁} (φ : A ⟶ B) (S : Profinite) :
  presheaf A S →+ presheaf B S :=
{ to_fun := λ f, ⟨φ ∘ f.1,
  begin
    obtain ⟨_, c, f, hf, rfl⟩ := f,
    refine ⟨c, (level.obj c).map φ ∘ f, (φ.level_continuous c).comp hf, rfl⟩,
  end⟩,
  map_zero' := by { ext, exact φ.map_zero },
  map_add' := by { intros, ext, exact φ.map_add _ _ } }

end presheaf

open opposite

-- we need to use `as_small Profiniteᵒᵖ`
def Presheaf (A : CompHausFiltPseuNormGrp₁) : Profiniteᵒᵖ ⥤ Ab :=
{ obj := λ S, ⟨presheaf A (unop S)⟩,
  map := λ S T φ, presheaf.comap A φ.unop,
  map_id' := sorry,
  map_comp' := sorry }

def Presheaf.map {A B : CompHausFiltPseuNormGrp₁} (φ : A ⟶ B) :
  Presheaf A ⟶ Presheaf B :=
{ app := λ S, presheaf.map φ (unop S),
  naturality' := by { intros, refl } }


def to_Condensed : CompHausFiltPseuNormGrp₁ ⥤ Condensed Ab :=
{ obj := λ A, { val := sorry, -- almost `Presheaf A`
  property := sorry }, -- ← this one will be hard
  map := sorry, -- almost `Presheaf.map`
  map_id' := sorry,
  map_comp' := sorry }

end CompHausFiltPseuNormGrp₁
