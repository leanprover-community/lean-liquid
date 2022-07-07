import condensed.filtered_colimits_commute_with_finite_limits
import condensed.ab
import condensed.short_exact
import condensed.bd_ses_aux
import for_mathlib.nnreal_to_nat_colimit
import for_mathlib.pow_functor

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

def presentation_point_isomorphism :
  F.obj ((as_nat_cocone A c).X) ≅ colimit (as_nat_diagram A c ⋙ F) :=
(is_colimit_of_preserves F (is_colimit_as_nat_cocone A c)).cocone_point_unique_up_to_iso
  (colimit.is_colimit _)

lemma coproduct_presentation_eq :
  coproduct_presentation F A c ≫ (presentation_point_isomorphism F A c).hom =
  coproduct_to_colimit ((as_nat_diagram A c ⋙ F)) :=
begin
  apply colimit.hom_ext, intros j,
  erw colimit.ι_desc,
  erw colimit.ι_desc_assoc,
  dsimp,
  erw (is_colimit_of_preserves F (is_colimit_as_nat_cocone A c)).fac,
  refl,
end

theorem coproduct_to_colimit_short_exact_sequence :
  short_exact (coproduct_to_coproduct (as_nat_diagram A c ⋙ F) - 𝟙 _)
  (coproduct_presentation F A c) :=
{ mono := infer_instance,
  epi := begin
    have := coproduct_presentation_eq F A c,
    rw ← iso.eq_comp_inv at this, rw this,
    apply_with epi_comp { instances := ff },
    apply_instance,
    apply_instance,
  end,
  exact := begin
    have := coproduct_presentation_eq F A c,
    rw ← iso.eq_comp_inv at this, rw this,
    rw exact_comp_iso,
    exact (short_exact_sequence_aux (as_nat_diagram A c ⋙ F)).exact,
  end }

variables (n : ℕ)

/-- The map `(∐ i, F((A_≤ i * c)^n)) ⟶ F(A^n)`. -/
def coproduct_presentation_with_pow :
  (∐ (λ i : as_small.{u+1} ℕ, F.obj (∏ λ (j : ulift.{u+1} (fin n)), (as_nat_diagram A c).obj i))) ⟶
  F.obj (∏ λ j : ulift.{u+1} (fin n), (as_nat_cocone A c).X) :=
sigma.desc $ λ i, F.map (pi.map $ λ j, (as_nat_cocone A c).ι.app i)

def as_nat_diagram_pow : as_small.{u+1} ℕ ⥤ CondensedSet.{u} :=
as_nat_diagram A c ⋙ pow_functor _ (ulift.{u+1} (fin n))

def as_nat_cocone_pow : cocone (as_nat_diagram_pow A c n) :=
(pow_functor _ (ulift.{u+1} (fin n))).map_cocone (as_nat_cocone A c)

def is_colimit_as_nat_cocone_pow : is_colimit (as_nat_cocone_pow A c n) :=
is_colimit_of_preserves _ (is_colimit_as_nat_cocone _ _)

def presentation_point_isomorphism_with_pow :
  F.obj (∏ λ (j : ulift.{u+1} (fin n)), (as_nat_cocone A c).X) ≅
  colimit (as_nat_diagram_pow A c n ⋙ F) :=
(is_colimit_of_preserves F
(is_colimit_as_nat_cocone_pow A c n)).cocone_point_unique_up_to_iso
(colimit.is_colimit _)

lemma coproduct_presentation_with_pow_eq :
  coproduct_presentation_with_pow F A c n =
  coproduct_to_colimit (as_nat_diagram_pow A c n ⋙ F) ≫
  (presentation_point_isomorphism_with_pow F A c n).inv :=
begin
  apply colimit.hom_ext, intros j,
  erw colimit.ι_desc,
  erw colimit.ι_desc_assoc,
  dsimp,
  erw colimit.ι_desc,
  refl,
end

/--
This is the short exact sequence of condensed abelian groups of the form
`0 → ∐ i, F((A_{c * i})^n) → ∐ i, F((A_{c * i})^n) → F(A^n) → 0`.
-/
def short_exact_sequence_with_pow :
  short_exact (coproduct_to_coproduct (as_nat_diagram_pow A c n ⋙ F) - 𝟙 _)
    (coproduct_presentation_with_pow F A c n) :=
{ mono := infer_instance,
  epi := begin
    rw coproduct_presentation_with_pow_eq,
    apply epi_comp,
  end,
  exact := begin
    rw coproduct_presentation_with_pow_eq,
    rw exact_comp_iso,
    exact (short_exact_sequence_aux _).exact,
  end }

end Condensed
