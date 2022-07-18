import for_mathlib.ab4
import for_mathlib.AddCommGroup

open category_theory
open category_theory.limits
namespace AddCommGroup

universe u

lemma injective_of_mono' {X Y : Ab.{u}} (f : X ⟶ Y) [mono f] :
  function.injective f :=
by rwa ← AddCommGroup.mono_iff_injective

open_locale classical

noncomputable
def cofan {α : Type (u)} (X : α → Ab.{u}) :
  cofan X :=
cofan.mk
(AddCommGroup.of $ Π₀ x, X x)
(λ a, dfinsupp.single_add_hom (λ x, X x) a)

noncomputable
def is_colimit_cofan {α : Type (u)} (X : α → Ab.{u}) :
  is_colimit (cofan X) :=
{ desc := λ S, dfinsupp.lift_add_hom
    (λ i, let e : X i ⟶ S.X := S.ι.app ⟨i⟩ in e),
  fac' := λ S j, begin
    cases j,
    dsimp [cofan], ext t,
    simp only [comp_apply, dfinsupp.single_add_hom_apply,
      dfinsupp.sum_add_hom_single],
  end,
  uniq' := begin
    intros S m hm,
    apply_fun dfinsupp.lift_add_hom.symm,
    swap, apply_instance,
    dsimp,
    erw add_equiv.symm_apply_apply, ext1 a,
    simp_rw ← hm,
    ext,
    dsimp [cofan],
    simp only [comp_apply, dfinsupp.single_add_hom_apply],
  end }

instance AB4 : AB4 AddCommGroup.{u} :=
begin
  constructor,
  introsI α X Y f hf,
  let t := _, change mono t,
  let eX : (∐ λ (a : α), X a) ≅ (cofan X).X :=
    (colimit.is_colimit _).cocone_point_unique_up_to_iso (is_colimit_cofan X),
  let eY : (∐ λ (a : α), Y a) ≅ (cofan Y).X :=
    (colimit.is_colimit _).cocone_point_unique_up_to_iso (is_colimit_cofan Y),
  let q : (cofan X).X ⟶ (cofan Y).X :=
    (is_colimit_cofan X).desc ⟨(cofan Y).X,
    λ a, f a.1 ≫ (cofan Y).ι.app a, _⟩,
  swap, { rintros ⟨i⟩ ⟨⟩ ⟨⟨⟨⟩⟩⟩, dsimp, simp, dsimp, simp },
  haveI : mono q,
  { apply concrete_category.mono_of_injective,
    rintros (u v : Π₀ x, X x) h, ext w,
    dsimp [q, is_colimit_cofan, cofan] at h,
    apply_fun (λ e, (e : Π₀ w, Y w) w) at h,
    simp_rw dfinsupp.sum_add_hom_apply at h,
    apply_fun f w,
    swap,
    { rw ← AddCommGroup.mono_iff_injective, apply_instance },
    let q : Π i, Y i → Π₀ i, Y i := dfinsupp.single,
    let qq : Π i, X i → Π₀ i, Y i := λ i, (q i) ∘ (f i),
    change u.sum (λ i, qq i) w = v.sum (λ i, qq i) w at h,
    rw @dfinsupp.sum_apply α (λ i, Y i) α _ (λ i, X i) _ _ _ u qq w at h,
    rw @dfinsupp.sum_apply α (λ i, Y i) α _ (λ i, X i) _ _ _ v qq w at h,
    simp only [dfinsupp.single_apply] at h,
    dsimp [dfinsupp.sum] at h,
    simp_rw [finset.sum_dite_eq'] at h,
    convert h,
    all_goals
    { split_ifs with hh hh, { refl },
      simp only [dfinsupp.mem_support_to_fun, not_not] at hh,
      simp only [hh, (f w).map_zero] } },
  suffices : t = eX.hom ≫ q ≫ eY.inv,
  { rw this, apply_instance },
  dsimp [t, eX, q, eY],
  apply colimit.hom_ext,
  rintro ⟨j⟩,
  simp only [colimit.ι_desc, cofan.mk_ι_app,
    is_colimit.cocone_point_unique_up_to_iso_hom_desc_assoc,
    colimit.is_colimit_desc, colimit.ι_desc_assoc, category.assoc,
    is_colimit.comp_cocone_point_unique_up_to_iso_inv, colimit.cocone_ι,
    eq_self_iff_true, implies_true_iff],
end

end AddCommGroup
