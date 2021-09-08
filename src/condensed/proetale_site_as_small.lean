/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import topology.category.Profinite
import category_theory.sites.pretopology
import category_theory.sites.sheaf_of_types
import category_theory.sites.sheaf
import category_theory.limits.opposites
import algebra.category.Group
import algebra.category.CommRing

import for_mathlib.pullbacks

/-!
# Proetale site of a point on Profinite

Defines the proetale site of a point on the category of Profinite sets.
-/
open category_theory category_theory.limits

universes v u

-- Generalize and move
instance : concrete_category (as_small.{u+1} Profinite.{u}) :=
{ forget := as_small.down ⋙ forget _,
  forget_faithful := {} } .

local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

instance : has_pullbacks (as_small.{u+1} Profinite.{u}) := as_small.equiv.has_pullbacks

section generalize_this

def point : as_small.{u+1} Profinite.{u} := as_small.up.obj $ Profinite.of punit

def from_point {X : as_small.{u+1} Profinite.{u}} :
  (point ⟶ X) ≃ X :=
{ to_fun := λ f, f punit.star,
  inv_fun := λ x, as_small.up.map ⟨λ _, x⟩,
  left_inv := λ x, by { ext ⟨⟩, refl },
  right_inv := λ x, rfl}

lemma from_point_apply {X Y : as_small.{u+1} Profinite.{u}} (f : point ⟶ X) (g : X ⟶ Y) :
  g (from_point f) = from_point (f ≫ g) :=
rfl

noncomputable def mk_pullback {X Y Z : as_small.{u+1} Profinite.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
  {x : X} {y : Y} (h : f x = g y) :
  (pullback f g : as_small.{u+1} Profinite.{u}) :=
from_point (pullback.lift (from_point.symm x) (from_point.symm y) (by { ext ⟨⟩, exact h }))

lemma mk_pullback_fst {X Y Z : as_small.{u+1} Profinite.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
  {x : X} {y : Y} {h : f x = g y} : (pullback.fst : pullback f g ⟶ _) (mk_pullback h) = x :=
begin
  rw [mk_pullback, from_point_apply],
  simp
end

lemma mk_pullback_snd {X Y Z : as_small.{u+1} Profinite.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
  {x : X} {y : Y} {h : f x = g y} : (pullback.snd : pullback f g ⟶ _) (mk_pullback h) = y :=
begin
  rw [mk_pullback, from_point_apply],
  simp
end

end generalize_this

/-- The proetale pretopology on Profinites. -/
def proetale_pretopology : pretopology.{u + 1} (as_small.{u+1} Profinite.{u}) :=
{ coverings := λ X S, ∃ (ι : Type (u + 1)) (_ : fintype ι)
      (Y : ι → as_small.{u+1} Profinite.{u}) (f : Π (i : ι), Y i ⟶ X),
      (∀ (x : X), ∃ i (y : (Y i)), (f i) y = x) ∧ S = presieve.of_arrows Y f,
  has_isos := λ X Y f i,
  begin
    refine ⟨punit, infer_instance, λ _, Y, λ _, f, _, _⟩,
    { introI x,
      refine ⟨punit.star, inv f x, _⟩,
      change (inv f ≫ _) x = x,
      rw [is_iso.inv_hom_id],
      simp },
    { rw presieve.of_arrows_punit },
  end,
  pullbacks := λ X Y f S,
  begin
    rintro ⟨ι, hι, Z, g, hg, rfl⟩,
    refine ⟨ι, hι, λ i, pullback (g i) f, λ i, pullback.snd, _, _⟩,
    { intro y,
      rcases hg (f y) with ⟨i, z, hz⟩,
      exact ⟨i, mk_pullback hz, mk_pullback_snd⟩ },
    { rw presieve.of_arrows_pullback }
  end,
  transitive := λ X S Ti,
  begin
    rintro ⟨ι, hι, Z, g, hY, rfl⟩ hTi,
    choose j hj W k hk₁ hk₂ using hTi,
    resetI,
    refine ⟨Σ (i : ι), j (g i) (presieve.of_arrows.mk _), infer_instance, λ i, W _ _ i.2, _, _, _⟩,
    { intro ij,
      exact k _ _ ij.2 ≫ g ij.1 },
    { intro x,
      obtain ⟨i, y, rfl⟩ := hY x,
      obtain ⟨i', z, rfl⟩ := hk₁ (g i) (presieve.of_arrows.mk _) y,
      refine ⟨⟨i, i'⟩, z, rfl⟩ },
    { have : Ti = λ Y f H, presieve.of_arrows (W f H) (k f H),
      { ext Y f H : 3,
        apply hk₂ },
      rw this,
      apply presieve.of_arrows_bind },
  end }

def proetale_topology : grothendieck_topology.{u+1} (as_small.{u+1} Profinite.{u}) :=
proetale_pretopology.to_grothendieck _

-- TODO (BM): We either want to generalise this topology to coherent? categories, or (less
-- generally) appropriate concrete categories; or (even less generally) repeat the construction for
-- ED and CH.
