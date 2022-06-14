import algebra.category.Group.biproducts
import algebra.category.Group.abelian
import algebra.direct_sum.basic
import category_theory.preadditive.yoneda
import for_mathlib.AddCommGroup.epi

open category_theory
open category_theory.limits

def dfinsupp.add_equiv_pi_on_fintype {α : Type*} [fintype α] (X : α → Type*)
  [∀ i, add_comm_group (X i)] :
  (Π₀ i, X i) ≃+ (Π i, X i) :=
{ map_add' := λ x y, by { ext, simp, },
  ..dfinsupp.equiv_fun_on_fintype }

namespace AddCommGroup

universes v u

def pi_π {α : Type v} (X : α → AddCommGroup.{max v u}) (i) :
  AddCommGroup.of (Π i, X i) ⟶ X i :=
pi.eval_add_monoid_hom _ _

def pi_fan {α : Type v} (X : α → AddCommGroup.{max v u}) : fan X :=
fan.mk (AddCommGroup.of $ Π i, X i)
(λ b, pi_π _ _)

def pi_lift {α : Type v} {Y : AddCommGroup.{max v u}} (X : α → AddCommGroup.{max v u})
  (f : Π a, Y ⟶ X a) : Y ⟶ AddCommGroup.of (Π i, X i) :=
{ to_fun := λ y i, f _ y,
  map_zero' := by { ext, simp },
  map_add' := λ x y, by { ext, simp } }

@[simp, reassoc]
lemma pi_lift_π {α : Type v} {Y : AddCommGroup.{max v u}} (X : α → AddCommGroup.{max v u})
  (f : Π a, Y ⟶ X a) (i) :
  pi_lift X f ≫ pi_π _ i = f _ := by { ext, refl }

lemma pi_hom_ext {α : Type v} {Y : AddCommGroup.{max v u}} (X : α → AddCommGroup.{max v u})
  (f g : Y ⟶ AddCommGroup.of (Π i, X i))
  (h : ∀ i, f ≫ pi_π _ i = g ≫ pi_π _ i) : f = g :=
by { ext y a, specialize h a, apply_fun (λ e, e y) at h, exact h }

def is_limit_pi_fan {α : Type v} (X : α → AddCommGroup.{max v u}) :
  is_limit (pi_fan X) :=
{ lift := λ S, pi_lift _ $ S.π.app,
  fac' := begin
    intros S j,
    apply pi_lift_π,
  end,
  uniq' := begin
    intros S m hm,
    apply pi_hom_ext,
    intros i,
    erw [hm, pi_lift_π],
  end }

noncomputable
def hom_product_comparison
  {α : Type v}
  (A : AddCommGroup.{max v u})
  (X : α → AddCommGroup.{max v u}) :
  AddCommGroup.of (A ⟶ ∏ X) ⟶ ∏ (λ i, AddCommGroup.of (A ⟶ (X i))) :=
limits.pi.lift $ λ a, (preadditive_yoneda.flip.obj (opposite.op A)).map (limits.pi.π _ _)

instance is_iso_hom_product_comparison
  {α : Type v}
  (A : AddCommGroup.{max v u})
  (X : α → AddCommGroup.{max v u}) :
  is_iso (hom_product_comparison A X) :=
begin
  --haveI : balanced Ab.{max v u} := AddcommGroup.abelian
  let t : (∏ λ (i : α), AddCommGroup.of (A ⟶ X i)) ≅ AddCommGroup.of
    (Π i, AddCommGroup.of (A ⟶ X i)) :=
    (limits.limit.is_limit _).cone_point_unique_up_to_iso
    (is_limit_pi_fan (λ i, of (A ⟶ X i))),
  suffices : is_iso (A.hom_product_comparison X ≫ t.hom),
  { apply is_iso.of_is_iso_comp_right _ t.hom, exact this },
  have ht : A.hom_product_comparison X ≫ t.hom =
    (is_limit_pi_fan (λ i, of (A ⟶ X i))).lift
    ⟨_, discrete.nat_trans $ λ i, (preadditive_yoneda.flip.obj (opposite.op A)).map
      (limits.pi.π _ _)⟩,
  { apply (is_limit_pi_fan _).hom_ext, intros j,
    simp [hom_product_comparison] },
  rw ht, clear ht,
  apply_with is_iso_of_mono_of_epi { instances := ff },
  apply_instance,
  { rw mono_iff_injective,
    intros f g h,
    ext1 j,
    apply_fun (λ e, e j) at h,
    exact h },
  { rw epi_iff_surjective,
    intros f,
    use limits.pi.lift (λ i, f i),
    dsimp [is_limit_pi_fan, pi_lift],
    simp [pi_lift_π] }
end

def direct_sum_π {α : Type v} (X : α → AddCommGroup.{max v u}) (i) :
  AddCommGroup.of (direct_sum α (λ i, X i)) ⟶ X i :=
{ to_fun := λ f, let e : Π₀ (i : α), (X i) := f in e i,
  map_zero' := by simp,
  map_add' := λ x y, by { dsimp, simp } }

def direct_sum_fan {α : Type v} (X : α → AddCommGroup.{max v u}) : fan X :=
fan.mk (AddCommGroup.of (direct_sum α (λ i, X i)))
(λ b, direct_sum_π _ _)

open_locale classical

def direct_sum_lift {α : Type v} [fintype α]
  {Y : AddCommGroup.{max v u}} (X : α → AddCommGroup.{max v u})
  (f : Π a, Y ⟶ X a) :
  Y ⟶ AddCommGroup.of (direct_sum α (λ i, X i)) :=
{ to_fun := λ y, (dfinsupp.add_equiv_pi_on_fintype _).symm $ λ i, f i y,
  map_zero' := begin
    simp_rw map_zero,
    change ((dfinsupp.add_equiv_pi_on_fintype (λ (i : α), ↥(X i))).symm) 0 = _,
    simp,
  end,
  map_add' := begin
    intros x y,
    simp_rw map_add,
    change ((dfinsupp.add_equiv_pi_on_fintype (λ (i : α), ↥(X i))).symm)
      ((λ (i : α), (f i) x) + (λ (i : α), (f i) y)) = _,
    simp,
  end }

@[simp, reassoc]
lemma direct_sum_lift_π {α : Type v} [fintype α]
  {Y : AddCommGroup.{max v u}} (X : α → AddCommGroup.{max v u})
  (f : Π a, Y ⟶ X a) (i) :
  direct_sum_lift X f ≫ direct_sum_π _ i = f i :=
by { ext, refl }

lemma direct_sum_hom_ext {α : Type v} [fintype α]
  {Y : AddCommGroup.{max v u}} (X : α → AddCommGroup.{max v u})
  (f g : Y ⟶ AddCommGroup.of (direct_sum α (λ i, X i)))
  (h : ∀ i, f ≫ direct_sum_π _ i = g ≫ direct_sum_π _ i) :
  f = g :=
begin
  ext,
  specialize h i,
  apply_fun (λ e, e x) at h, exact h
end

def is_limit_direct_sum_fan {α : Type v} [fintype α]
  (X : α → AddCommGroup.{max v u}) : is_limit (direct_sum_fan X) :=
{ lift := λ S, direct_sum_lift _ $ S.π.app,
  fac' := begin
    intros S j,
    apply direct_sum_lift_π,
  end,
  uniq' := begin
    intros S m hm,
    apply direct_sum_hom_ext,
    intros i,
    specialize hm i,
    erw [hm, direct_sum_lift_π],
  end }

noncomputable theory

def to_direct_sum {α : Type v} (X : α → AddCommGroup.{max v u})
  (i : α) : X i ⟶ AddCommGroup.of (direct_sum α (λ i, X i)) :=
direct_sum.of (λ i, X i) i

def direct_sum_punit_iso (A : AddCommGroup.{max v u}) :
  AddCommGroup.of (direct_sum _ (λ i : punit.{v+1}, A)) ≅ A :=
{ hom := direct_sum_π _ punit.star,
  inv := to_direct_sum (λ i, A) punit.star,
  hom_inv_id' := begin
    ext ⟨⟩ ⟨⟩,
    ext t ⟨⟩, -- WAT?
    dsimp [direct_sum_π, to_direct_sum],
    simp,
  end,
  inv_hom_id' := begin
    ext a,
    dsimp [direct_sum_π, to_direct_sum],
    simp,
  end }

def direct_sum_ι {α : Type v} (X : α → AddCommGroup.{max v u})
  (i : α) : X i ⟶ AddCommGroup.of (direct_sum α (λ i, X i)) :=
direct_sum.of _ i

def direct_sum_desc {α : Type v} {Y : AddCommGroup.{max v u}} (X : α → AddCommGroup.{max v u})
  (f : Π i, X i ⟶ Y) :
  AddCommGroup.of (direct_sum α (λ i, X i)) ⟶ Y :=
direct_sum.to_add_monoid f

@[simp, reassoc]
lemma direct_sum_ι_desc {α : Type v} {Y : AddCommGroup.{max v u}}
  (X : α → AddCommGroup.{max v u})
  (f : Π i, X i ⟶ Y) (i) :
  direct_sum_ι X i ≫ direct_sum_desc X f = f _ :=
by { ext, dsimp [direct_sum_ι, direct_sum_desc], simp }

lemma direct_sum_hom_ext' {α : Type v} {Y : AddCommGroup.{max v u}}
  (X : α → AddCommGroup.{max v u})
  (f g : AddCommGroup.of (direct_sum α (λ i, X i)) ⟶ Y)
  (h : ∀ i, direct_sum_ι X i ≫ f = direct_sum_ι X i ≫ g) :
  f = g :=
begin
  have hf : f = direct_sum_desc X (λ i, direct_sum_ι X i ≫ f),
  { ext t, apply direct_sum.to_add_monoid.unique },
  have hg : g = direct_sum_desc X (λ i, direct_sum_ι X i ≫ g),
  { ext t, apply direct_sum.to_add_monoid.unique },
  rw [hf, hg],
  congr' 1, ext i, rw h,
end

def direct_sum_cofan {α : Type v}
  (X : α → AddCommGroup.{max v u}) : cofan X :=
cofan.mk _ (direct_sum_ι _)

def is_colimit_direct_sum_cofan {α : Type v}
  (X : α → AddCommGroup.{max v u}) : is_colimit (direct_sum_cofan X) :=
{ desc := λ S, direct_sum_desc X S.ι.app,
  fac' := begin
    intros X j,
    apply direct_sum_ι_desc,
  end,
  uniq' := begin
    intros S m hm,
    apply direct_sum_hom_ext',
    intros i,
    specialize hm i,
    erw hm, rw direct_sum_ι_desc,
  end }

lemma direct_sum_ι_π {α : Type v} (X : α → AddCommGroup.{max v u}) (i : α) :
  direct_sum_ι.{v u} X i ≫ direct_sum_π.{v u} X i = 𝟙 _ :=
begin
  ext,
  dsimp [direct_sum_ι, direct_sum_π, direct_sum.of],
  simp only [comp_apply, dfinsupp.single_add_hom_apply, add_monoid_hom.coe_mk,
    dfinsupp.single_apply],
  split_ifs, refl, refl,
end

lemma direct_sum_ι_π_of_ne {α : Type v} (X : α → AddCommGroup.{max v u}) (i j : α) (h : i ≠ j):
  direct_sum_ι.{v u} X i ≫ direct_sum_π.{v u} X j = 0 :=
begin
  ext,
  dsimp [direct_sum_ι, direct_sum_π, direct_sum.of],
  simp only [comp_apply, dfinsupp.single_add_hom_apply, add_monoid_hom.coe_mk,
    dfinsupp.single_apply],
  split_ifs, contradiction, refl,
end

-- `bicone` is not sufficiently universe polymorphic.
def direct_sum_bicone {α : Type u} [fintype α]
  (X : α → AddCommGroup.{u}) : bicone X :=
{ X := AddCommGroup.of (direct_sum α (λ i, X i)),
  π := direct_sum_π.{u u} _,
  ι := direct_sum_ι.{u u} _,
  ι_π := λ i j, begin
    ext t,
    dsimp [direct_sum_ι, direct_sum_π, direct_sum.of],
    simp only [comp_apply, dfinsupp.single_add_hom_apply, add_monoid_hom.coe_mk,
      dfinsupp.single_apply],
    split_ifs, subst h, refl, refl,
  end }

def is_bilimit_direct_sum_bicone {α : Type u} [fintype α]
  (X : α → AddCommGroup.{u}) :
  bicone.is_bilimit (direct_sum_bicone X) :=
{ is_limit := is_limit_direct_sum_fan.{u u} X,
  is_colimit := is_colimit_direct_sum_cofan.{u u} X }

end AddCommGroup
