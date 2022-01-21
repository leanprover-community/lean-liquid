import condensed.extr.basic
import condensed.proetale_site
import condensed.basic
import category_theory.sites.induced_topology

import for_mathlib.presieve

open category_theory

universes u v' u'

set_option pp.universes true

def ExtrDisc.cover_dense :
  cover_dense proetale_topology.{u} ExtrDisc_to_Profinite.{u} :=
  cover_dense.mk $ λ U,
begin
  change ∃ R, _,
  obtain ⟨⟨T,hT,π,hπ⟩⟩ := enough_projectives.presentation U,
  dsimp at hT hπ,
  let R : presieve U := presieve.of_arrows (λ i : punit, T) (λ i, π),
  use R,
  split,
  { refine ⟨punit, infer_instance, λ i, T, λ i, π, λ x, ⟨punit.star, _⟩, rfl⟩,
    rw Profinite.epi_iff_surjective at hπ,
    exact hπ x },
  intros Y f hf,
  change nonempty _,
  rcases hf with ⟨a,b⟩,
  let t : presieve.cover_by_image_structure ExtrDisc_to_Profinite π := _,
  swap,
  { resetI,
    refine ⟨⟨T⟩, 𝟙 _, π, by simp⟩ },
  use t,
end

def ExtrDisc.proetale_topology : grothendieck_topology ExtrDisc.{u} :=
  ExtrDisc.cover_dense.induced_topology.{u}

@[derive category]
def ExtrSheaf (C : Type u') [category.{v'} C] := Sheaf ExtrDisc.proetale_topology.{u} C

def Condensed_ExtrSheaf_equiv (C : Type u') [category.{u+1} C] [limits.has_limits C] :
  ExtrSheaf.{u} C ≌ Condensed.{u} C := sorry
--cover_dense.Sheaf_equiv C (ExtrDisc.cover_dense.{u})  <--- universe issues.
-- Will be fixed using mathlib PR #11588

--theorem ExtrSheaf_iff (C : Type u') [category.{v'} C] [limits.has_limits C]
--  (F : ExtrDiscᵒᵖ ⥤ C) : presheaf.is_sheaf ExtrDisc.proetale_topology F ↔

open opposite

def is_ExtrSheaf_of_types (P : ExtrDisc.{u}ᵒᵖ ⥤ Type u') : Prop :=
∀ (B : ExtrDisc.{u}) (ι : Type u) [fintype ι] (α : ι → ExtrDisc.{u})
  (f : Π i, α i ⟶ B) (hf : ∀ b : B, ∃ i (x : α i), f i x = b)
  (x : Π i, P.obj (op (α i)))
  (hx : ∀ (i j : ι) (Z : ExtrDisc) (g₁ : Z ⟶ α i) (g₂ : Z ⟶ α j),
    g₁ ≫ f _ = g₂ ≫ f _ → P.map g₁.op (x _) = P.map g₂.op (x _)),
∃! t : P.obj (op B), ∀ i, P.map (f i).op t = x _

-- This is more or less proved in the profinite case, along with a condition
-- that equalizers should be compatible, while the equalizer condition in the
-- ExtrDisc case can be found (in some form) in `condensed/extr.lean`.
-- It will take some time to convert these proofs to this case, but this is
-- very doable!
theorem ExtrSheaf_iff_is_ExtrSheaf_of_types
  (F : ExtrDiscᵒᵖ ⥤ Type u') :
  presieve.is_sheaf ExtrDisc.proetale_topology F ↔
  is_ExtrSheaf_of_types F :=
begin
  split,
  { introsI H B ι _ X f hf x hx,
    let S : presieve B := presieve.of_arrows X f,
    specialize H (sieve.generate S) _,
    { sorry },
    rw ← presieve.is_sheaf_for_iff_generate at H,
    let t : S.family_of_elements F := presieve.mk_family_of_elements_of_arrows X f F x,
    have ht : t.compatible := presieve.mk_family_of_elements_of_arrows_compatible X f F x hx,
    specialize H t ht,
    -- now use H.
    sorry,
  },
  { sorry }
end
