import Lbar.torsion_free_profinite
import condensed.condensify

noncomputable theory

universe u

open category_theory opposite

open_locale nnreal

namespace CompHausFiltPseuNormGrp

lemma to_Condensed_torsion_free (M : CompHausFiltPseuNormGrp) [no_zero_smul_divisors ℤ M]
  (T : ExtrDisc) :
  no_zero_smul_divisors ℤ ((to_Condensed.obj M).val.obj (op T.val)) :=
begin
  dsimp, constructor,
  intros n f hf,
  rw or_iff_not_imp_left,
  intro hn,
  ext t,
  apply_fun (λ φ, φ.down.val t) at hf,
  apply smul_right_injective M hn,
  dsimp [presheaf.has_zero] at hf ⊢,
  convert hf using 1,
  apply smul_zero
end

end CompHausFiltPseuNormGrp

namespace Lbar

variables (r' : ℝ≥0) [fact (0 < r')]

lemma Fintype_Lbar_torsion_free (X : Fintype) :
  no_zero_smul_divisors ℤ ((Fintype_Lbar r' ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r').obj X) :=
Fintype.Lbar_no_zero_smul_divisors _ _

lemma condensify_torsion_free (A : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁)
  (hA : ∀ X, no_zero_smul_divisors ℤ (A.obj X))
  (S : Profinite) (T : ExtrDisc.{u}) :
  no_zero_smul_divisors ℤ (((condensify A).obj S).val.obj (op T.val)) :=
begin
  apply_with CompHausFiltPseuNormGrp.to_Condensed_torsion_free {instances := ff},
  apply Profinite.extend_torsion_free,
  apply hA,
end

def condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
condensify (Fintype_Lbar.{u u} r' ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r')

instance (S : Profinite.{u}) (T : ExtrDisc.{u}) :
  no_zero_smul_divisors ℤ (((condensed.{u} r').obj S).val.obj (op T.val)) :=
condensify_torsion_free _ (Fintype_Lbar_torsion_free r') _ _

end Lbar
