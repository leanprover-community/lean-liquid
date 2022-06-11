import algebra.category.Module.adjunctions
import group_theory.free_abelian_group_finsupp
import algebra.category.Group.adjunctions
import algebra.category.Group.filtered_colimits
import algebra.category.Group.abelian

open category_theory

universes u

namespace AddCommGroup

noncomputable theory

@[simps]
def free' : Type u ⥤ AddCommGroup.{u} :=
{ obj := λ X, AddCommGroup.of $ X →₀ ℤ,
  map := λ X Y f, finsupp.map_domain.add_monoid_hom f,
  map_id' := begin
    intros X, ext, dsimp, simp,
  end,
  map_comp' := begin
    intros X Y Z f g, ext, dsimp, simp,
  end } .

@[simps]
def of_iso {A B : Type u} [add_comm_group A] [add_comm_group B]
  (e : A ≃+ B) : of A ≅ of B :=
{ hom := e.to_add_monoid_hom,
  inv := e.symm.to_add_monoid_hom,
  hom_inv_id' := begin
    ext, dsimp, simp,
  end,
  inv_hom_id' := begin
    ext, dsimp, simp,
  end } .

@[simps]
def free_iso_free' : free.{u} ≅ free'.{u} :=
category_theory.nat_iso.of_components
(λ X, of_iso (free_abelian_group.equiv_finsupp X))
begin
  intros X Y f, ext, dsimp, simp,
end

def adj' : free'.{u} ⊣ forget AddCommGroup.{u} :=
AddCommGroup.adj.of_nat_iso_left $ free_iso_free'.{u}

end AddCommGroup

def types.pt {α : Type u} (a : α) : ⊥_ _ ⟶ α :=
λ x, a

namespace AddCommGroup

def tunit : AddCommGroup.{u} :=
  AddCommGroup.free'.obj (⊥_ _)

def tunit.lift {A : AddCommGroup.{u}} (e : ⊥_ _ ⟶ (forget _).obj A) :
  tunit ⟶ A :=
(AddCommGroup.adj'.hom_equiv _ _).symm e

open_locale classical

def hom_of_basis {ι : Type u} {A : AddCommGroup.{u}} (𝓑 : basis ι ℤ A) :
  (∐ (λ i : ι, tunit.{u})) ⟶ A :=
limits.sigma.desc $ λ b, tunit.lift $ types.pt (𝓑 b)

instance is_iso_hom_of_basis {ι : Type u} (A : AddCommGroup.{u}) (𝓑 : basis ι ℤ A) :
  is_iso (hom_of_basis 𝓑) := sorry

def iso_of_basis {ι : Type u} {A : AddCommGroup.{u}} (𝓑 : basis ι ℤ A) :
  (∐ (λ i : ι, tunit.{u})) ≅ A :=
as_iso (hom_of_basis 𝓑)

@[derive partial_order]
def index_cat (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] : Type u :=
{ H : add_subgroup A // H.fg } -- Is this the condition we want?

instance semilattice_sup (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] :
  semilattice_sup A.index_cat :=
{ sup := λ I J, ⟨I.1 ⊔ J.1, sorry⟩,
  le_sup_left := λ I J, @le_sup_left (add_subgroup A) _ _ _,
  le_sup_right := λ I J, @le_sup_right (add_subgroup A) _ _ _,
  sup_le := λ I J K h1 h2, @sup_le (add_subgroup A) _ _ _ _ h1 h2,
  ..(infer_instance : partial_order _) }

def diagram (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] :
  A.index_cat ⥤ AddCommGroup.{u} :=
{ obj := λ I, AddCommGroup.of I.1,
  map := λ I J h, add_subgroup.inclusion h.le,
  map_id' := sorry,
  map_comp' := sorry }

def cocone (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] :
  limits.cocone A.diagram :=
{ X := A,
  ι :=
  { app := λ I, I.1.subtype,
    naturality' := sorry } }

def is_colimit_cocone (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] :
  limits.is_colimit A.cocone :=
{ desc := λ S,
  { to_fun := λ a, S.ι.app ⟨add_subgroup.closure {a}, sorry⟩
      ⟨a, add_subgroup.subset_closure rfl⟩,
    map_zero' := sorry,
    map_add' := sorry },
  fac' := sorry,
  uniq' := sorry }

def colimit_comparison (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] :
  limits.colimit A.diagram ≅ A :=
(limits.colimit.is_colimit A.diagram).cocone_point_unique_up_to_iso
  A.is_colimit_cocone

lemma exists_basis_of_index (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A]
  (I : A.index_cat) : ∃ (ι : Type u) [fintype ι]
  (𝓑 : basis ι ℤ (AddCommGroup.of I.1)), true := sorry

lemma exists_sigma_iso_of_index (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A]
  (I : A.index_cat) : ∃ (ι : Type u) [fintype ι]
  (e : (∐ (λ i : ι, tunit.{u})) ≅ AddCommGroup.of I.1), true := sorry

end AddCommGroup
