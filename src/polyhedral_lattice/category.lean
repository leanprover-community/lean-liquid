import polyhedral_lattice.basic
import category_theory.concrete_category.bundled_hom
import for_mathlib.SemiNormedGroup
/-

# The category of polyhedral lattices

-/
universe variables u

open category_theory

/-- The category of polyhedral lattices and bounded group homomorphisms. -/
@[derive has_coe_to_sort]
def PolyhedralLattice : Type (u+1) := bundled polyhedral_lattice

namespace PolyhedralLattice

variables (Λ : PolyhedralLattice)

instance : polyhedral_lattice Λ := Λ.str

def to_SemiNormedGroup : SemiNormedGroup := SemiNormedGroup.of Λ

instance bundled_hom : bundled_hom @polyhedral_lattice_hom :=
⟨@polyhedral_lattice_hom.to_fun,
@polyhedral_lattice_hom.id, @polyhedral_lattice_hom.comp, @polyhedral_lattice_hom.coe_inj⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] PolyhedralLattice

/-- Construct a bundled `PolyhedralLattice` from the underlying type and typeclass. -/
def of (Λ : Type u) [polyhedral_lattice Λ] : PolyhedralLattice := bundled.of Λ

-- noncomputable
-- instance : has_zero PolyhedralLattice := ⟨of punit⟩

-- noncomputable
-- instance : inhabited PolyhedralLattice := ⟨0⟩

@[simp] lemma coe_of (Λ : Type u) [polyhedral_lattice Λ] :
  (PolyhedralLattice.of Λ : Type u) = Λ := rfl

@[simp] lemma coe_id (Λ : PolyhedralLattice) : ⇑(𝟙 Λ) = id := rfl

instance : limits.has_zero_morphisms.{u (u+1)} PolyhedralLattice :=
{ comp_zero' := by { intros, ext, refl },
  zero_comp' := by { intros _ _ _ f, ext, exact f.map_zero } }

def iso_mk {Λ₁ Λ₂ : PolyhedralLattice.{u}}
  (f : Λ₁ →+ Λ₂) (g : Λ₂ → Λ₁) (hf : ∀ l, ∥f l∥ = ∥l∥) (hfg : g ∘ f = id) (hgf : f ∘ g = id) :
  Λ₁ ≅ Λ₂ :=
{ hom := { strict' := λ l, le_of_eq (hf l), ..f },
  inv :=
  { strict' := λ l,
    calc ∥g l∥ ≤ ∥f (g l)∥ : le_of_eq $ (hf _).symm
    ... = ∥l∥ : congr_arg norm $ congr_fun hgf l,
    .. add_equiv.symm
    { inv_fun := g,
      left_inv := congr_fun hfg,
      right_inv := congr_fun hgf,
      .. f } },
  hom_inv_id' := by { ext x, exact congr_fun hfg x },
  inv_hom_id' := by { ext x, exact congr_fun hgf x } }

end PolyhedralLattice
