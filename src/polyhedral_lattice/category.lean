import polyhedral_lattice.basic
import category_theory.concrete_category.bundled_hom
import normed_group.NormedGroup

universe variables u

open category_theory

/-- The category of polyhedral lattices and bounded group homomorphisms. -/
@[derive has_coe_to_sort]
def PolyhedralLattice : Type (u+1) := bundled polyhedral_lattice

namespace PolyhedralLattice

variables (Λ : PolyhedralLattice)

instance : polyhedral_lattice Λ := Λ.str

def to_NormedGroup : NormedGroup := NormedGroup.of Λ

noncomputable
instance : large_category PolyhedralLattice :=
induced_category.category to_NormedGroup

-- should we set things up differently, so that we automatically get a `concrete_category`?

/-- Construct a bundled `PolyhedralLattice` from the underlying type and typeclass. -/
def of (Λ : Type u) [polyhedral_lattice Λ] : PolyhedralLattice := bundled.of Λ

-- noncomputable
-- instance : has_zero PolyhedralLattice := ⟨of punit⟩

-- noncomputable
-- instance : inhabited PolyhedralLattice := ⟨0⟩

@[simp] lemma coe_of (Λ : Type u) [polyhedral_lattice Λ] :
  (PolyhedralLattice.of Λ : Type u) = Λ := rfl

@[simp] lemma coe_id (Λ : NormedGroup) : ⇑(𝟙 Λ) = id := rfl

noncomputable
instance : limits.has_zero_morphisms.{u (u+1)} PolyhedralLattice :=
{ comp_zero' := by { intros, apply normed_group_hom.zero_comp },
  zero_comp' := by { intros, apply normed_group_hom.comp_zero } }

end PolyhedralLattice
