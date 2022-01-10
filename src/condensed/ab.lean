import category_theory.abelian.projective
import pseudo_normed_group.category
import topology.continuous_function.algebra

import for_mathlib.abelian_sheaves.main

import condensed.adjunctions

/-!
# Properties of the category of condensed abelian groups

-/

open category_theory category_theory.limits

universes v u

namespace Condensed

--instance : preadditive (Condensed Ab.{u+1}) := sorry

noncomputable theory

-- Sanity check
example {J : Type (u+1)} [small_category J] [is_filtered J] :
  limits.preserves_colimits_of_shape J (forget Ab.{u+1}) := by apply_instance

instance : enough_projectives (Condensed Ab.{u+1}) := sorry

instance : is_right_adjoint (Sheaf_to_presheaf _ _ : Condensed Ab.{u+1} ⥤ _) :=
{ left := presheaf_to_Sheaf _ _,
  adj := (sheafification_adjunction _ _) }

def forget_to_CondensedType : Condensed Ab.{u+1} ⥤ CondensedSet :=
{ obj := λ F, ⟨F.val ⋙ forget _, begin
    cases F with F hF,
    rw (presheaf.is_sheaf_iff_is_sheaf_forget _ _ (forget Ab)) at hF,
    rw ← is_sheaf_iff_is_sheaf_of_type,
    assumption,
    apply_instance
  end ⟩,
  map := λ A B f, ⟨whisker_right f.val _⟩ }

instance : is_right_adjoint forget_to_CondensedType :=
{ left := CondensedSet_to_Condensed_Ab,
  adj := Condensed_Ab_CondensedSet_adjunction }

section

variables (A : Type (u+1)) [add_comm_group A] [topological_space A] [topological_add_group A]

def of_top_ab.presheaf : Profiniteᵒᵖ ⥤ Ab :=
{ obj := λ S, ⟨C(S.unop, A)⟩,
  map := λ S₁ S₂ f, add_monoid_hom.mk' (λ g, g.comp f.unop) $ λ g₁ g₂, rfl,
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }

/-- The condensed abelian group associated with a topological abelian group -/
def of_top_ab : Condensed.{u} Ab :=
{ val := of_top_ab.presheaf A,
  cond := sorry }

end

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
  exact continuous_nsmul _ _ _ hf,
end⟩

protected def zsmul (n : ℤ) (f : presheaf A S) : presheaf A S :=
⟨n • f.1,
begin
  obtain ⟨_, c, f, hf, rfl⟩ := f,
  refine ⟨n.nat_abs * c, λ s, ⟨n • f s, int_smul_mem_filtration _ _ _ (f s).2⟩, _, rfl⟩,
  exact continuous_zsmul _ _ _ hf,
end⟩

variables (A S)

instance : add_comm_group (presheaf A S) :=
{ zero := 0,
  add := (+),
  nsmul := presheaf.nsmul,
  zsmul := presheaf.zsmul,
  add_assoc := by { intros, ext, exact add_assoc _ _ _ },
  zero_add := by { intros, ext, exact zero_add _ },
  add_zero := by { intros, ext, exact add_zero _ },
  add_comm := by { intros, ext, exact add_comm _ _ },
  add_left_neg := by { intros, ext, exact add_left_neg _ },
  sub_eq_add_neg := by { intros, ext, exact sub_eq_add_neg _ _ },
  nsmul_zero' := by { intros, ext, exact zero_nsmul _ },
  nsmul_succ' := by { intros, ext, exact succ_nsmul _ _ },
  zsmul_zero' := by { intros, ext, exact zero_zsmul _ },
  zsmul_succ' := by { intros, ext, exact add_comm_group.zsmul_succ' _ _ },
  zsmul_neg' := by { intros, ext, exact add_comm_group.zsmul_neg' _ _ },
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
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }

def Presheaf.map {A B : CompHausFiltPseuNormGrp₁} (φ : A ⟶ B) :
  Presheaf A ⟶ Presheaf B :=
{ app := λ S, presheaf.map φ (unop S),
  naturality' := by { intros, refl } }

@[simp]
lemma Presheaf.map_id (A : CompHausFiltPseuNormGrp₁) :
  Presheaf.map (𝟙 A) = 𝟙 _ := by { ext, refl }

@[simp]
lemma Presheaf.map_comp {A B C : CompHausFiltPseuNormGrp₁} (f : A ⟶ B) (g : B ⟶ C) :
  Presheaf.map (f ≫ g) = Presheaf.map f ≫ Presheaf.map g := by { ext, refl }

set_option pp.universes true

def to_Condensed : CompHausFiltPseuNormGrp₁.{u+1} ⥤ Condensed.{u} Ab :=
{ obj := λ A,
  { val := Presheaf A,
    cond := sorry }, -- ← this one will be hard
  map := λ A B f, ⟨Presheaf.map f⟩,
  map_id' := λ X, by { ext : 2, dsimp, simp },
  map_comp' := λ X Y Z f g, by { ext : 2, dsimp, simp } }

end CompHausFiltPseuNormGrp₁
