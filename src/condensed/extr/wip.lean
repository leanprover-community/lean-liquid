import condensed.extr.basic
import condensed.proetale_site
import condensed.basic
import category_theory.sites.induced_topology

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

-- This is more or less proved in the profinite case, along with a condition
-- that equalizers should be compatible, while the equalizer condition in the
-- ExtrDisc case can be found (in some form) in `condensed/extr.lean`.
-- It will take some time to convert these proofs to this case, but this is
-- very doable!
theorem ExtrSheaf_iff (C : Type u') [category.{v'} C] [limits.has_limits C]
  (F : ExtrDiscᵒᵖ ⥤ C) :
  presheaf.is_sheaf ExtrDisc.proetale_topology F ↔
  (ExtrDisc.terminal_condition F ∧ ExtrDisc.binary_product_condition F) := sorry
