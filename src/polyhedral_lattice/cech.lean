import algebraic_topology.simplicial_object

import polyhedral_lattice.finsupp
import polyhedral_lattice.category

import for_mathlib.free_abelian_group
import for_mathlib.normed_group_quotient
import for_mathlib.finsupp
import for_mathlib.normed_group

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

-- jmc : I don't think we need this one
-- lemma L_zero : L f 0 = ⊥ := by admit

@[simp] lemma L_one : L f 1 = ⊥ :=
begin
  refine add_subgroup.closure_eq_of_le ⊥ _ bot_le,
  simp only [and_imp, exists_prop, set.subset_singleton_iff, finsupp.map_range_hom_apply,
    add_subgroup.coe_bot, set.mem_set_of_eq, exists_imp_distrib, finsupp.sum,
    add_monoid_hom.id_apply],
  rintro _ l n hn rfl,
  suffices : n = 0, { simp only [this, finsupp.map_range_zero] },
  ext i, fin_cases i,
  simp only [finsupp.coe_zero, pi.zero_apply, ← hn],
  have aux : ∀ s : finset (fin 1), s = ∅ ∨ s = {0}, { dec_trivial },
  cases aux n.support with h' h',
  { simp only [h', finset.sum_empty, ← finsupp.not_mem_support_iff, finset.not_mem_empty, not_false_iff] },
  { simp only [h', finset.sum_singleton], }
end

def obj := quotient_add_group.quotient (L f m)

instance : semi_normed_group (obj f m) :=
normed_group_hom.semi_normed_group_quotient _

instance : polyhedral_lattice (obj f m) :=
{ finite_free := sorry, -- we will need some sort of torsion-free condition on the cokernel of `f`
  polyhedral :=
  begin
    obtain ⟨ι, _inst_ι, l, hl, hl'⟩ := polyhedral_lattice.polyhedral (fin m →₀ Λ'),
    refine ⟨ι, _inst_ι, (λ i, quotient_add_group.mk (l i)), _, _⟩,
    { intros x,
      apply quotient_add_group.induction_on x; clear x,
      intro x,
      obtain ⟨d, hd, c, H1, H2⟩ := hl x,
      refine ⟨d, hd, c, _, _⟩,
      { show d • quotient_add_group.mk' _ x = _,
        rw [← add_monoid_hom.map_nsmul, H1, add_monoid_hom.map_sum],
        simp only [add_monoid_hom.map_nsmul], refl, },
      { dsimp,
        sorry } },
    { sorry }
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
  rw [set_like.mem_coe, add_subgroup.mem_comap],
  apply add_subgroup.subset_closure,
  refine ⟨l, c.map_domain g, _, _⟩,
  { rwa sum_map_domain_index_add_monoid_hom },
  { simp only [← add_monoid_hom.comp_apply, ← map_range_hom_map_domain_hom], refl }
end

-- the underlying morphism of additive groups
def map_add_hom : obj f (n+1) →+ obj f (m+1) :=
quotient_add_group.map _ _ (map_domain_hom g) (L_le_comap f g)

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
    simp only [finset.sum_ite_eq, finset.mem_univ, if_true], }
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

open polyhedral_lattice simplex_category category_theory

variables {Λ Λ' : PolyhedralLattice.{u}} (f : Λ ⟶ Λ')

namespace Cech_conerve

def obj (m : ℕ) : PolyhedralLattice := of (conerve.obj f (m+1))

def map_succ_zero_aux (m : ℕ) (g : fin (m+2) →ₘ fin 1) : obj f (m+1) →+ Λ' :=
(finsupp.apply_add_hom (0 : fin 1)).comp $
begin
  -- TODO: this is very ugly
  let foo := quotient_add_group.lift (conerve.L f (m + 1 + 1)) (finsupp.map_domain_hom g),
  refine foo _,
  intros x hx,
  rw ← add_monoid_hom.mem_ker,
  revert hx x,
  apply (add_subgroup.closure_le _).mpr _,
  rintro _ ⟨l, c, hc, rfl⟩,
  dsimp,
  rw [set_like.mem_coe, add_monoid_hom.mem_ker, ← finsupp.map_range_hom_apply,
    ← add_monoid_hom.comp_apply, ← finsupp.map_range_hom_map_domain_hom, add_monoid_hom.comp_apply],
  suffices : finsupp.map_domain g c = 0,
  { rw [finsupp.map_domain_hom_apply, this, add_monoid_hom.map_zero] },
  ext i,
  simp only [finsupp.map_domain, finsupp.sum_apply, finsupp.single_apply],
  convert hc,
  ext,
  rw if_pos, { refl },
  exact subsingleton.elim _ _
end

def map_succ_zero (m : ℕ) (g : fin (m+2) →ₘ fin 1) : obj f (m+1) ⟶ Λ' :=
{ strict' :=
  begin
    intro x,
    apply le_of_forall_pos_le_add,
    intros ε hε,
    obtain ⟨x, rfl, h⟩ := normed_group_hom.norm_mk_lt x hε,
    calc ∥finsupp.map_domain_hom g x 0∥
        ≤ ∥finsupp.map_domain_hom g x∥ : _
    ... ≤ ∥x∥ : conerve.map_domain_hom_strict g x
    ... ≤ _ : h.le,
    rw [finsupp.norm_def, finsupp.sum_eq_sum_fintype, fin.sum_univ_succ, fin.sum_univ_zero, add_zero],
    intro, exact norm_zero
  end,
  .. map_succ_zero_aux f m g }

-- def map : Π ⦃m n : ℕ⦄ (g : fin (m+1) →ₘ fin (n+1)), obj f m ⟶ obj f n
-- | 0     0     g := 𝟙 _
-- | 0     (n+1) g := map_zero_succ f n g
-- | (m+1) 0     g := map_succ_zero f m g
-- | (m+1) (n+1) g := conerve.map f g

-- move this, generalize to arbitrary subsingletons
lemma preorder_hom_eq_id (g : fin 1 →ₘ fin 1) : g = preorder_hom.id :=
by { ext1, exact subsingleton.elim _ _ }

-- @[simp] lemma map_zero_zero (g : fin 1 →ₘ fin 1) : map f g = 𝟙 _ := rfl

-- lemma map_id : ∀ m, map f (preorder_hom.id : fin (m+1) →ₘ fin (m+1)) = 𝟙 _
-- | 0     := rfl
-- | (m+1) := conerve.map_id f

-- lemma map_comp : ∀ k m n (g : fin (k+1) →ₘ fin (m+1)) (g' : fin (m+1) →ₘ fin (n+1)),
--   map f (g'.comp g) = map f g ≫ map f g'
-- | 0     0     0     g g' := (category.id_comp _).symm
-- | 0     0     (n+1) g g' := by { rw [preorder_hom_eq_id g], refl }
-- | 0     (m+1) 0     g g' := by { rw [preorder_hom_eq_id (g'.comp g), map_id], admit }
-- | 0     (m+1) (n+1) g g' := by { admit }
-- | (k+1) 0     0     g g' := by { rw [preorder_hom_eq_id g'], refl }
-- | (k+1) 0     (n+1) g g' :=
-- begin
--   ext x, apply quotient_add_group.induction_on x; clear x,
--   intro x, admit
-- end
-- | (k+1) (m+1) 0     g g' :=
-- begin
--   ext x, apply quotient_add_group.induction_on x; clear x,
--   intro x, admit
-- end
-- | (k+1) (m+1) (n+1) g g' := conerve.map_comp f _ _

end Cech_conerve

open Cech_conerve

@[simps]
def Cech_conerve : simplex_category ⥤ PolyhedralLattice :=
{ obj := λ n, obj f n.len,
  map := λ n m g, conerve.map f g.to_preorder_hom,
  map_id' := λ _, conerve.map_id f,
  map_comp' := λ _ _ _ _ _, conerve.map_comp f _ _ }


@[simps]
def augmentation_map_aux (n : ℕ) (g : fin 1 →ₘ fin (n+1)) : Λ' ⟶ obj f n :=
{ strict' := λ l,
  begin
    calc _ ≤ ∥(finsupp.single (g 0)) l∥ : normed_group_hom.quotient_norm_mk_le _ _
    ... ≤ ∥l∥ : _,
    rw [finsupp.norm_def, finsupp.sum_single_index],
    exact norm_zero
  end,
  .. (quotient_add_group.mk' $ conerve.L _ _).comp (finsupp.single_add_hom (g 0)) }

def Cech_augmentation_map : Λ ⟶ (Cech_conerve f).obj (mk 0) :=
f ≫ augmentation_map_aux f 0 preorder_hom.id

lemma augmentation_map_equalizes :
  Cech_augmentation_map f ≫ (Cech_conerve f).map (δ 0) =
  Cech_augmentation_map f ≫ (Cech_conerve f).map (δ 1) :=
begin
  sorry
  /-
  ext l,
  show augmentation_map_aux f 1 (δ 0) (f l) = augmentation_map_aux f 1 (δ 1) (f l),
  simp only [Cech_conerve.map_zero_succ_apply, add_monoid_hom.coe_comp,
    add_monoid_hom.to_fun_eq_coe, finsupp.single_add_hom_apply, function.comp_app,
    quotient_add_group.mk'_eq_mk'_iff],
  apply add_subgroup.subset_closure,
  refine ⟨l, finsupp.single 1 1 - finsupp.single 0 1, _, _⟩,
  { rw [finsupp.sum_eq_sum_fintype],
    swap, { intro, refl },
    simp only [fin.sum_univ_succ, fin.sum_univ_zero, add_zero, finsupp.sub_apply,
      add_monoid_hom.id_apply, finsupp.single_apply, fin.one_eq_zero_iff,
      if_true, zero_sub, fin.zero_eq_one_iff, eq_self_iff_true, sub_zero, fin.succ_zero_eq_one,
      add_left_neg, if_false, one_ne_zero] },
  { simp only [add_monoid_hom.map_sub],
    simp only [finsupp.map_range_hom_apply, finsupp.map_range_single, int.cast_add_hom'_one],
    refl }
  -/
end

end PolyhedralLattice
