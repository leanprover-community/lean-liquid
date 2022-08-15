import banach
import real_measures.condensed
import condensed.projective_resolution
import for_mathlib.Profinite.extend
import for_mathlib.abelian_category
import for_mathlib.derived.K_projective

open_locale nnreal
open opposite category_theory

universe u

noncomputable theory

variables (p' p : ℝ≥0) [fact (0 < p')] [fact (p' ≤ 1)] [fact (p' < p)]

section
open tactic
meta def tactic.extract_facts : tactic unit := do
  ctx ← local_context,
  ctx.mmap' $ λ hyp, do
    hyp_tp ← infer_type hyp,
    when (hyp_tp.is_app_of `fact) $
      mk_app `fact.out [hyp] >>= note_anon none >> skip

meta def tactic.interactive.fact_arith : tactic unit :=
tactic.extract_facts >>
`[norm_cast at *,
  simp only [← nnreal.coe_lt_coe, ← nnreal.coe_le_coe] at *,
  refine fact.mk _,
  linarith]
end

meta def tactic.interactive.fact_arith₂ :=
 tactic.interactive.fact_arith <|> `[apply_instance]

localized "notation `ℳ_{` p' `}` S := (@real_measures.condensed p' _ (by fact_arith₂)).obj S"
  in liquid_tensor_experiment

abbreviation liquid_tensor_experiment.Ext (i : ℤ) (A B : Condensed.{u} Ab.{u+1}) :=
((Ext' i).obj (op A)).obj B

instance : has_coe (pBanach.{u} p) (Condensed.{u} Ab.{u+1}) :=
{ coe := λ V, Condensed.of_top_ab V }

abbreviation liquid_tensor_experiment.sections (F : Condensed.{0} Ab.{1}) (S : Profinite.{0}) :
  Ab.{1} := F.val.obj (opposite.op S)

localized "notation `Γ_` := liquid_tensor_experiment.sections" in liquid_tensor_experiment

def pBanach.has_coe_to_fun_condensed_eval (V : pBanach.{0} p) (S : Profinite.{0}) :
  has_coe_to_fun (Γ_ (V : Condensed.{0} Ab.{1}) S) (λ _, S → V) :=
⟨λ f, ((ulift.down f : C(S,V)) : S → V)⟩

localized "attribute [instance] pBanach.has_coe_to_fun_condensed_eval" in
  liquid_tensor_experiment
