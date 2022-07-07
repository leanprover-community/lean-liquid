import condensed.filtered_colimits_commute_with_finite_limits
import condensed.ab
import condensed.short_exact
import for_mathlib.nnreal_to_nat_colimit

open category_theory
open category_theory.limits

namespace Condensed

open_locale nnreal
open opposite

noncomputable theory

universes u
variables (F : CondensedSet.{u} ⥤ Condensed.{u} Ab.{u+1})
  [preserves_filtered_colimits F] (A : CompHausFiltPseuNormGrp.{u})
  (c : ℝ≥0) [fact (0 < c)]

set_option pp.universes true

def as_nat_diagram : as_small.{u+1} ℕ ⥤ CondensedSet.{u} :=
restrict_diagram c A.level_Condensed_diagram'

@[simp, reassoc]
lemma ι_colimit_iso_Condensed_obj (i) :
  colimit.ι _ i ≫ A.colimit_iso_Condensed_obj.hom =
  A.level_Condensed_diagram_cocone.ι.app _ :=
begin
  dsimp [CompHausFiltPseuNormGrp.colimit_iso_Condensed_obj],
  erw colimit.ι_desc_assoc,
  apply CondensedSet_to_presheaf.map_injective,
  dsimp [CompHausFiltPseuNormGrp.colimit_iso_Condensed_obj_aux_nat_iso],
  ext S : 2, dsimp,
  erw
    ((is_colimit_of_preserves.{u+1 u+1 u+1 u+1 u+2 u+2}
    ((category_theory.evaluation.{u u+1 u+1 u+2} Profinite.{u}ᵒᵖ
    (Type (u+1))).obj S) (colimit.is_colimit.{u+1 u+1 u+1 u+2}
    (A.level_Condensed_diagram' ⋙ Sheaf_to_presheaf.{u u+1 u+1 u+2}
    proetale_topology.{u} (Type (u+1)))))).fac_assoc,
  erw colimit.ι_desc_assoc,
  refl,
end

def is_colimit_level_Condensed_diagram_cocone :
  is_colimit A.level_Condensed_diagram_cocone :=
{ desc := λ S, A.colimit_iso_Condensed_obj.inv ≫ colimit.desc _ S,
  fac' := begin
    intros S j, rw ← category.assoc,
    let t := _, change t ≫ _ = _,
    have ht : t = colimit.ι _ _,
    { dsimp [t], rw [iso.comp_inv_eq, ι_colimit_iso_Condensed_obj] },
    simp [ht],
  end,
  uniq' := begin
    intros S m hm,
    rw iso.eq_inv_comp,
    apply colimit.hom_ext, intros j,
    specialize hm j,
    simpa,
  end }

def as_nat_cocone : cocone (as_nat_diagram A c) :=
restrict_cocone c A.level_Condensed_diagram_cocone

def is_colimit_as_nat_cocone : is_colimit (as_nat_cocone A c) :=
is_colimit_restrict_cocone c _ (is_colimit_level_Condensed_diagram_cocone _)

/-- The map `∐ F(A_≤(n * c)) ⟶ F(A)`-/
def coproduct_presentation :
  (∐ (λ i : as_small.{u+1} ℕ, F.obj ((as_nat_diagram A c).obj i))) ⟶
  F.obj (as_nat_cocone A c).X :=
sigma.desc $ λ i, F.map ((as_nat_cocone A c).ι.app i)

instance epi_coproduct_presentation :
  epi (coproduct_presentation F A c) :=
begin
  let G : cocone (as_nat_diagram A c ⋙ F) :=
    F.map_cocone (as_nat_cocone A c),
  let hG : is_colimit G := is_colimit_of_preserves F (is_colimit_as_nat_cocone _ _),
  let e : F.obj (as_nat_cocone A c).X ≅ G.X :=
    (is_colimit_of_preserves F (is_colimit_as_nat_cocone A c)).cocone_point_unique_up_to_iso hG,
  suffices : epi (coproduct_presentation F A c ≫ e.hom),
  { exact (epi_iso_comp_iff_epi (coproduct_presentation F A c) e).mp this },
  constructor, intros Z a b w,
  apply hG.hom_ext, intros j,
  apply_fun (λ e, sigma.ι
    (λ i : as_small.{u+1} ℕ, F.obj ((as_nat_diagram A c).obj i)) j ≫ e) at w,
  convert w using 1,
  all_goals
  { dsimp [coproduct_presentation, e],
    simp only [category.assoc, colimit.ι_desc_assoc], dsimp,
    erw (is_colimit_of_preserves.{u+1 u+1 u+1 u+1 u+2 u+2} F
      (is_colimit_as_nat_cocone.{u} A c)).fac_assoc,
    refl },
end

def coproduct_to_coproduct :
  (∐ (λ i : as_small.{u+1} ℕ, F.obj ((as_nat_diagram A c).obj i))) ⟶
  (∐ (λ i : as_small.{u+1} ℕ, F.obj ((as_nat_diagram A c).obj i))) :=
sigma.desc $ λ i, F.map ((as_nat_diagram A c).map $
  as_small.up.map $ hom_of_le $ nat.le_succ _) ≫
  sigma.ι (λ i : as_small.{u+1} ℕ, F.obj ((as_nat_diagram A c).obj i))
  (ulift.up $ (ulift.down i) + 1)

open opposite

def coproduct_eval_iso {α : Type (u+1)} (X : α → Condensed.{u} Ab.{u+1}) (S : ExtrDisc.{u}) :
  (∐ X).val.obj (op S.val) ≅ ∐ (λ a, (X a).val.obj (op S.val)) :=
preserves_colimit_iso (Condensed.evaluation Ab.{u+1} S.val) _ ≪≫
has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ _, iso.refl _)

instance mono_coproduct_to_coproduct :
  mono (coproduct_to_coproduct F A c - 𝟙 _) :=
begin
  rw mono_iff_ExtrDisc,
  intros S, dsimp,
  sorry -- TODO: same proof that we did in the other file...
end

end Condensed
