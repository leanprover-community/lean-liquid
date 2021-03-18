import algebraic_topology.simplicial_object

import polyhedral_lattice.finsupp
import polyhedral_lattice.category

import for_mathlib.free_abelian_group
import for_mathlib.normed_group_quotient
import for_mathlib.finsupp

/-!
# The Čech conerve attached to `Λ → Λ'`

Let `f : Λ → Λ'` be a morphism of polyhedral lattices.
(We probably need to assume that the cokernel is torsion-free...)

In this file we construct the Čech conerve attached to `f`.

Concretely, but in pseudo-code:
it consists of the objects `Λ'^(m)` defined as `(Λ')^m/L`,
where `L` is the sublattice `Λ ⊗ {x : ℤ^m | ∑ x = 0}`.
-/

noncomputable theory

open_locale big_operators

local attribute [-instance] add_comm_monoid.nat_semimodule add_comm_group.int_module

namespace polyhedral_lattice

variables {Λ Λ' : Type*} [polyhedral_lattice Λ] [polyhedral_lattice Λ']
variables (f : polyhedral_lattice_hom Λ Λ')

namespace conerve

section objects

/-!
## The objects
-/

variables (m : ℕ)

def L : add_subgroup (fin m →₀ Λ') :=
add_subgroup.closure $
{x | ∃ (l : Λ) (n : fin m →₀ ℤ) (hn : n.sum (λ _, add_monoid_hom.id _) = 0),
     x = finsupp.map_range_hom (int.cast_add_hom' (f l)) n}

def obj := quotient_add_group.quotient (L f m)

-- we can remove this as soon as we have `seminormed_group`
instance : is_closed (L f m : set (fin m →₀ Λ')) := sorry

instance : normed_group (obj f m) :=
normed_group_hom.normed_group_quotient _

instance : polyhedral_lattice (obj f m) :=
{ nat_semimodule := add_comm_monoid.nat_semimodule,
  int_semimodule := add_comm_group.int_module,
  is_scalar_tower := by convert add_comm_monoid.nat_is_scalar_tower,
  finite_free := sorry, -- we will need some sort of torsion-free condition on the cokernel of `f`
  polyhedral :=
  begin
    obtain ⟨ι, _inst_ι, l, hl⟩ := polyhedral_lattice.polyhedral (fin m →₀ Λ'),
    refine ⟨ι, _inst_ι, (λ i, quotient_add_group.mk (l i)), _⟩,
    intros x,
    apply quotient_add_group.induction_on x; clear x,
    intro x,
    obtain ⟨d, hd, c, H1, H2⟩ := hl x,
    refine ⟨d, hd, c, _, _⟩,
    { show d • quotient_add_group.mk' _ x = _,
      rw [← nsmul_eq_smul, ← add_monoid_hom.map_nsmul, nsmul_eq_smul, H1,
        add_monoid_hom.map_sum],
      apply fintype.sum_congr,
      intro i,
      rw [← nsmul_eq_smul, add_monoid_hom.map_nsmul],
      exact @nsmul_eq_smul _ _ add_comm_monoid.nat_semimodule _ _ },
    { dsimp,
      sorry }
  end }

end objects

section maps

/-!
## The simplicial maps
-/

open finsupp

variables {n m k : ℕ} (g : fin (n+1) → fin (m+1)) (g' : fin (m+1) → fin (k+1))

lemma L_le_comap : (L f (n+1)) ≤ (L f (m+1)).comap (map_domain_hom g) :=
begin
  rw [L, add_subgroup.closure_le],
  rintros _ ⟨l, c, hc, rfl⟩,
  rw [add_subgroup.mem_coe, add_subgroup.mem_comap],
  apply add_subgroup.subset_closure,
  refine ⟨l, c.map_domain g, _, _⟩,
  { rwa sum_map_domain_index_add_monoid_hom },
  { simp only [← add_monoid_hom.comp_apply, ← map_range_hom_map_domain_hom], refl }
end

-- the underlying morphism of additive groups
def map_add_hom : obj f (n+1) →+ obj f (m+1) :=
quotient_add_group.map _ _ (map_domain_hom g) (L_le_comap f g)

-- move this
@[simp] lemma norm_ite {V : Type*} [normed_group V] (P : Prop) {hP : decidable P} (x y : V) :
  ∥(if P then x else y)∥ = if P then ∥x∥ else ∥y∥ :=
by split_ifs; refl

lemma map_domain_hom_strict (x : fin (n+1) →₀ Λ) : ∥map_domain_hom g x∥ ≤ ∥x∥ :=
begin
  simp only [norm_def, map_domain_hom_apply],
  dsimp [map_domain],
  rw [sum_eq_sum_fintype], swap, { intro, exact norm_zero },
  simp only [sum_apply],
  rw [sum_eq_sum_fintype], swap, { intro, exact norm_zero },
  calc ∑ i, ∥x.sum (λ j l, single (g j) l i)∥
      ≤ ∑ i, ∑ j, ∥single (g j) (x j) i∥ : _
  ... ≤ ∑ j, ∥x j∥ : _,
  { apply finset.sum_le_sum,
    rintro i -,
    rw sum_eq_sum_fintype, swap, { intro, rw [single_zero, zero_apply] },
    exact norm_sum_le _ _ },
  { rw finset.sum_comm,
    apply finset.sum_le_sum,
    rintro j -,
    simp only [single_apply, norm_ite, norm_zero],
    apply le_of_eq,
    have := @finset.sum_ite_eq _ ℝ _ _ finset.univ (g j) (λ _, ∥x j∥),
    simp only [finset.mem_univ, if_true] at this,
    convert this, ext, split_ifs; refl, }
end

lemma map_add_hom_strict (x : obj f (n+1)) : ∥map_add_hom f g x∥ ≤ ∥x∥ :=
begin
  apply le_of_forall_pos_le_add,
  intros ε hε,
  obtain ⟨x, rfl, h⟩ := normed_group_hom.norm_mk_lt x hε,
  calc _ ≤ ∥map_domain_hom g x∥ : normed_group_hom.quotient_norm_mk_le _ _
  ... ≤ ∥x∥ : map_domain_hom_strict _ _
  ... ≤ _ : h.le,
end

lemma map_add_hom_mk (x : fin (n+1) →₀ Λ') :
  (map_add_hom f g) (quotient_add_group.mk x) = quotient_add_group.mk (map_domain_hom g x) :=
rfl

@[simps]
def map : polyhedral_lattice_hom (obj f (n+1)) (obj f (m+1)) :=
{ strict' := map_add_hom_strict f g,
  .. map_add_hom f g }

lemma map_id : map f (id : fin (m+1) → fin (m+1)) = polyhedral_lattice_hom.id :=
begin
  ext x,
  apply quotient_add_group.induction_on x; clear x,
  intro x,
  simp only [add_monoid_hom.to_fun_eq_coe, map_apply, polyhedral_lattice_hom.id_apply,
    map_add_hom_mk, map_domain_hom_apply, map_domain_id],
end

lemma map_comp : map f (g' ∘ g) = (map f g').comp (map f g) :=
begin
  ext x,
  apply quotient_add_group.induction_on x; clear x,
  intro x,
  simp only [add_monoid_hom.to_fun_eq_coe, map_apply, polyhedral_lattice_hom.comp_apply,
    map_add_hom_mk, map_domain_hom_apply, ← map_domain_comp],
end

end maps

end conerve

end polyhedral_lattice

namespace PolyhedralLattice

universe variables u

open polyhedral_lattice simplex_category

variables {Λ Λ' : PolyhedralLattice.{u}} (f : Λ ⟶ Λ')

@[simps]
def Cech_conerve : simplex_category ⥤ PolyhedralLattice :=
{ obj := λ m, of (conerve.obj f (m+1)),
  map := λ n m g, conerve.map f g,
  map_id' := λ m, conerve.map_id f,
  map_comp' := λ _ _ _ g g', conerve.map_comp f _ _ }

def Cech_augmentation_map : Λ ⟶ (Cech_conerve f).obj (mk 0) :=
sorry

end PolyhedralLattice
