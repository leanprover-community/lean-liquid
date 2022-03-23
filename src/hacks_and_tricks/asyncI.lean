namespace tactic

meta def prove_goal_asyncI (tac : tactic unit) : tactic unit := do
ctx ← local_context, unfreezing (revert_lst ctx),
tgt ← target, tgt ← instantiate_mvars tgt,
env ← get_env, tgt ← return $ env.unfold_untrusted_macros tgt,
when tgt.has_meta_var (fail "goal contains metavariables"),
params ← return tgt.collect_univ_params,
lemma_name ← new_aux_decl_name,
proof ← run_async (do
  goal_meta ← mk_meta_var tgt,
  set_goals [goal_meta],
  ctx.mmap' (λc, unfreezing (intro c.local_pp_name)),
  tac,
  proof ← instantiate_mvars goal_meta,
  proof ← return $ env.unfold_untrusted_macros proof,
  when proof.has_meta_var $ fail "async proof failed: contains metavariables",
  return proof),
add_decl $ declaration.thm lemma_name params tgt proof,
exact (expr.const lemma_name (params.map level.param))

namespace interactive
open interactive.types

/-- Proves the first goal asynchronously as a separate lemma. -/
meta def asyncI (tac : itactic) : tactic unit :=
prove_goal_asyncI tac

end interactive
end tactic

