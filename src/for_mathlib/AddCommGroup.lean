import algebra.category.Module.adjunctions
import group_theory.free_abelian_group_finsupp
import algebra.category.Group.adjunctions
import algebra.category.Group.filtered_colimits
import algebra.category.Group.abelian
import category_theory.limits.preserves.shapes.products
import category_theory.limits.preserves.filtered
import linear_algebra.free_module.pid

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

instance nonempty_index_cat (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] :
  nonempty A.index_cat := ⟨⟨⊥, ∅, by simp⟩⟩

instance semilattice_sup_index_cat
  (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] :
  semilattice_sup A.index_cat :=
{ sup := λ I J, ⟨I.1 ⊔ J.1, begin
    obtain ⟨S,hS⟩ := I.2,
    obtain ⟨T,hT⟩ := J.2,
    rw [← hS, ← hT],
    use S ∪ T,
    simp only [finset.coe_union, add_subgroup.closure_union],
  end⟩,
  le_sup_left := λ I J, @le_sup_left (add_subgroup A) _ _ _,
  le_sup_right := λ I J, @le_sup_right (add_subgroup A) _ _ _,
  sup_le := λ I J K h1 h2, @sup_le (add_subgroup A) _ _ _ _ h1 h2,
  ..(infer_instance : partial_order _) }

def diagram (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] :
  A.index_cat ⥤ AddCommGroup.{u} :=
{ obj := λ I, AddCommGroup.of I.1,
  map := λ I J h, add_subgroup.inclusion h.le }

def cocone (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] :
  limits.cocone A.diagram :=
{ X := A,
  ι := { app := λ I, I.1.subtype } }

def is_colimit_cocone (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] :
  limits.is_colimit A.cocone :=
{ desc := λ S,
  { to_fun := λ a, S.ι.app ⟨add_subgroup.closure {a}, {a}, by simp⟩
      ⟨a, add_subgroup.subset_closure rfl⟩,
    map_zero' := add_monoid_hom.map_zero _,
    map_add' := λ x y, sorry },
  fac' := sorry,
  uniq' := sorry }

def colimit_comparison (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A] :
  limits.colimit A.diagram ≅ A :=
(limits.colimit.is_colimit A.diagram).cocone_point_unique_up_to_iso
  A.is_colimit_cocone

lemma exists_basis_of_index (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A]
  (I : A.index_cat) : ∃ (ι : Type u) [fintype ι]
  (𝓑 : basis ι ℤ (AddCommGroup.of I.1)), true :=
begin
  obtain ⟨S,hS⟩ := I.2,
  let e : S → I.1 := λ s, ⟨s,_⟩,
  swap, { rw ← hS, apply add_subgroup.subset_closure, exact s.2 },
  haveI : no_zero_smul_divisors ℤ I.1,
  { constructor, rintros c ⟨x, hx⟩ h, apply_fun (λ e, e.val) at h,
    dsimp at h,
    cases no_zero_smul_divisors.eq_zero_or_eq_zero_of_smul_eq_zero h,
    left, assumption,
    right, ext, assumption },
  obtain ⟨n,B⟩ := @module.free_of_finite_type_torsion_free S ℤ _ _ _ I.1 _ _ _ e _ _,
  { use [ulift (fin n), infer_instance],
    refine ⟨_, trivial⟩,
    apply B.reindex,
    exact equiv.ulift.symm },
  { apply le_antisymm, { intros x hx, trivial },
    rintros x -,
    rw ← hS at x,
    sorry },
end

lemma exists_sigma_iso_of_index (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A]
  (I : A.index_cat) : ∃ (ι : Type u) [fintype ι]
  (e : (∐ (λ i : ι, tunit.{u})) ≅ AddCommGroup.of I.1), true :=
begin
  obtain ⟨ι,hι,𝓑,-⟩ := exists_basis_of_index A I,
  use [ι, hι, iso_of_basis 𝓑],
end

lemma exists_biprod_iso_of_index (A : AddCommGroup.{u}) [no_zero_smul_divisors ℤ A]
  (I : A.index_cat) : ∃ (ι : Type u) [fintype ι]
  (e : by exactI (⨁ (λ i : ι, tunit.{u})) ≅ AddCommGroup.of I.1), true :=
begin
  obtain ⟨ι,hι,e,-⟩ := exists_sigma_iso_of_index A I,
  resetI, use [ι, hι],
  use (limits.biproduct.is_bilimit _).is_colimit.cocone_point_unique_up_to_iso
      (limits.colimit.is_colimit _) ≪≫ e,
end

universes u'

lemma is_iso_of_preserves {𝓐 : Type u'} [category.{u} 𝓐] [preadditive 𝓐]
  (F G : AddCommGroup ⥤ 𝓐)
  [F.additive]
  [G.additive]
  [limits.preserves_filtered_colimits F]
  [limits.preserves_filtered_colimits G]
  (η : F ⟶ G)
  [hη : is_iso (η.app tunit)]
  (A : AddCommGroup.{u})
  [no_zero_smul_divisors ℤ A] :
  is_iso (η.app A) :=
begin
  let T := (limits.cocones.precompose (whisker_left A.diagram η)).obj
    (G.map_cocone A.cocone),
  let S := F.map_cocone A.cocone,
  let hS : limits.is_colimit S :=
    limits.is_colimit_of_preserves F A.is_colimit_cocone,
  have : η.app A = hS.desc T,
  { apply hS.hom_ext, intros j, rw hS.fac,
    dsimp, apply η.naturality },
  rw this, clear this,
  suffices : ∀ I : A.index_cat, is_iso (η.app (A.diagram.obj I)),
  { resetI,
    haveI : is_iso (whisker_left A.diagram η),
    { apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
      intros I, exact this I },
    let hT : limits.is_colimit T :=
      (limits.is_colimit.precompose_hom_equiv (as_iso (whisker_left A.diagram η))
      (G.map_cocone A.cocone)).symm (limits.is_colimit_of_preserves G A.is_colimit_cocone),
    use hT.desc S,
    split,
    { apply hS.hom_ext,
      intros j,
      erw [hS.fac_assoc, hT.fac, category.comp_id] },
    { apply hT.hom_ext,
      intros j,
      erw [hT.fac_assoc, hS.fac, category.comp_id] }
  }, --^ general colimit nonsense..., but I can't find applicable lemmas :-(
  intros I,
  obtain ⟨ι,hι,e,-⟩ := A.exists_biprod_iso_of_index I,
  -- now use the fact that the functors are additive and that there exists some iso with a biproduct
  resetI,
  let eF : F.obj (⨁ λ (i : ι), tunit.{u}) ≅ ⨁ λ (i : ι), F.obj tunit :=
    (limits.is_bilimit_of_preserves F
    (limits.biproduct.is_bilimit (λ i : ι, tunit.{u}))).is_colimit.cocone_point_unique_up_to_iso
    (limits.biproduct.is_bilimit (λ i : ι, F.obj tunit)).is_colimit,
  let eG : G.obj (⨁ λ (i : ι), tunit.{u}) ≅ ⨁ λ (i : ι), G.obj tunit :=
    (limits.is_bilimit_of_preserves G
    (limits.biproduct.is_bilimit (λ i : ι, tunit.{u}))).is_colimit.cocone_point_unique_up_to_iso
    (limits.biproduct.is_bilimit (λ i : ι, G.obj tunit)).is_colimit,
  have : η.app (A.diagram.obj I) =
    F.map e.inv ≫ eF.hom ≫ limits.biproduct.desc
      (λ i, η.app _ ≫ limits.biproduct.ι _ i) ≫ eG.inv ≫ G.map e.hom,
  { rw [← functor.map_iso_inv, iso.eq_inv_comp, ← iso.inv_comp_eq],
    apply limits.biproduct.hom_ext', intros i,
    simp only [functor.map_iso_hom, nat_trans.naturality,
      limits.biproduct.ι_desc_assoc, category.assoc],
    erw [limits.biproduct.ι_desc_assoc, limits.biproduct.ι_desc_assoc],
    dsimp, rw η.naturality_assoc },
  rw this,
  apply_with is_iso.comp_is_iso { instances := ff },
  apply_instance,
  apply_with is_iso.comp_is_iso { instances := ff },
  apply_instance,
  apply_with is_iso.comp_is_iso { instances := ff },
  swap,
  apply_instance,
  use limits.biproduct.desc
      (λ i, inv (η.app _) ≫ limits.biproduct.ι _ i),
  split,
  { ext, simp },
  { ext, simp },
end

end AddCommGroup
