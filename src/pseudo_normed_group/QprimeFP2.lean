import pseudo_normed_group.FP2
import condensed.adjunctions
import free_pfpng.acyclic
import for_mathlib.derived.ext_coproducts
import for_mathlib.derived.example
import breen_deligne.eval2
import system_of_complexes.shift_sub_id
import for_mathlib.AddCommGroup.explicit_products
import condensed.Qprime_isoms
import condensed.short_exact
import condensed.bd_ses

noncomputable theory

open_locale nnreal

universe u

open category_theory category_theory.limits breen_deligne

section step1

variables (r' : ℝ≥0)
variables (BD : breen_deligne.data) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

abbreviation freeCond := Profinite_to_Condensed.{u} ⋙ CondensedSet_to_Condensed_Ab

def QprimeFP_nat : ℝ≥0 ⥤ chain_complex (Condensed.{u} Ab.{u+1}) ℕ :=
FPsystem r' BD ⟨M⟩ κ ⋙ (freeCond.{u}.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _

def QprimeFP_int : ℝ≥0 ⥤ cochain_complex (Condensed.{u} Ab.{u+1}) ℤ :=
QprimeFP_nat r' BD κ M ⋙ homological_complex.embed complex_shape.embedding.nat_down_int_up

def QprimeFP : ℝ≥0 ⥤ bounded_homotopy_category (Condensed.{u} Ab.{u+1}) :=
QprimeFP_nat r' BD κ M ⋙ chain_complex.to_bounded_homotopy_category

variable {r'}
def ProFiltPseuNormGrpWithTinv₁.to_Condensed : Condensed.{u} Ab.{u+1} :=
(PFPNGT₁_to_CHFPNG₁ₑₗ r' ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u} ⋙
  CompHausFiltPseuNormGrp.to_Condensed.{u}).obj M
variable (r')

end step1
namespace QprimeFP

variables (r' : ℝ≥0)
variables (BD : breen_deligne.package) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (ι : ℕ →o ℝ≥0)

def coproduct_to_coproduct :
  (∐ λ (k : as_small.{u+1} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj
    (ι $ as_small.down.obj k)) ⟶
  (∐ λ (k : as_small.{u+1} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj
    (ι $ as_small.down.obj k)) :=
begin
  refine sigma.desc (λ i, _),
  refine _ ≫ sigma.ι _ (as_small.up.obj $ as_small.down.obj i + 1),
  refine (QprimeFP_int r' BD.data κ M).map _,
  refine hom_of_le (ι.2 _),
  refine nat.le_succ _,
end

def coproduct_eval_iso (i : ℤ) :
  (∐ λ (k : as_small.{u+1} ℕ), (QprimeFP_int.{u} r' BD.data κ M).obj
    (ι $ as_small.down.obj k)).X i ≅
  (∐ λ (k : as_small.{u+1} ℕ), ((QprimeFP_int.{u} r' BD.data κ M).obj
    (ι $ as_small.down.obj k)).X i) :=
begin
  refine preserves_colimit_iso (homological_complex.eval _ _ _) _ ≪≫ _,
  refine has_colimit.iso_of_nat_iso _,
  refine discrete.nat_iso _,
  intros k, exact iso.refl _,
end

lemma coproduct_to_coproduct_eq (i : ℕ) :
  (coproduct_to_coproduct r' BD κ M ι).f i =
  (coproduct_eval_iso r' BD κ M ι i).hom ≫
  Condensed.coproduct_to_coproduct
  (as_small.down ⋙ nat_to_nnreal ι ⋙
  QprimeFP_int r' BD.data κ M ⋙
  homological_complex.eval _ _ i) ≫
  (coproduct_eval_iso r' BD κ M ι i).inv :=
begin
  dsimp only [coproduct_to_coproduct, Condensed.coproduct_to_coproduct,
    coproduct_eval_iso],
  apply (is_colimit_of_preserves
    (homological_complex.eval (Condensed.{u} Ab.{u+1}) (complex_shape.up ℤ) i)
    (colimit.is_colimit _)).hom_ext,
  intros j, swap, apply_instance,
  dsimp, rw [← homological_complex.comp_f, colimit.ι_desc],
  slice_rhs 1 2
  { erw (is_colimit_of_preserves
      (homological_complex.eval (Condensed.{u} Ab.{u+1}) (complex_shape.up ℤ) i)
      (colimit.is_colimit _)).fac },
  dsimp,
  slice_rhs 1 2
  { erw colimit.ι_desc },
  dsimp,
  simp only [category.assoc, category.id_comp],
  slice_rhs 1 2
  { erw colimit.ι_desc },
  dsimp,
  slice_rhs 2 3
  { erw colimit.ι_desc },
  dsimp,
  slice_rhs 3 4
  { erw colimit.ι_desc },
  erw category.id_comp,
  refl,
end

.

def package_eval_cocone : cocone (QprimeFP_int r' BD.data κ M) :=
{ X := (BD.eval' freeCond').obj M.to_Condensed,
  ι :=
  { app := λ s,
    { f := λ i,
      match i with
      | int.of_nat 0 := _
      | int.of_nat (i+1) := 0
      | -[1+i] := begin
          dsimp [QprimeFP_int, QprimeFP_nat],
          let t := (Condensed.eval_freeCond'_iso.component_neg BD M.to_Condensed i),
          refine _ ≫ t.inv,
          dsimp [FreeAb.eval, functor.map_FreeAb, CondensedSet_to_Condensed_Ab],
          refine presheaf_to_Condensed_Ab.map _,
          dsimp [package.eval'],
          refine _ ≫ (functor.associator _ _ _).hom,
          refine whisker_right _ _,
          dsimp [FPsystem, FPsystem.X],
          sorry

        end
      end,
      comm' := _ },
    naturality' := _ } }

--  (BD.eval' freeCond').obj M.to_Condensed :=

end QprimeFP
