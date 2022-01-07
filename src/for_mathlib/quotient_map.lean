import data.setoid.basic
import topology.homeomorph

variables {α β : Type*} [topological_space α] [topological_space β]

noncomputable theory

def quotient_map.homeomorph {f : α → β} (hf : quotient_map f) : quotient (setoid.ker f) ≃ₜ β :=
{ continuous_to_fun := quotient_map_quot_mk.continuous_iff.mpr hf.continuous,
  continuous_inv_fun := begin
    rw hf.continuous_iff,
    convert continuous_quotient_mk,
    ext,
    simpa [(setoid.quotient_ker_equiv_of_surjective f (quotient_map.surjective hf)).symm_apply_eq],
  end,
  ..(setoid.quotient_ker_equiv_of_surjective _ hf.surjective) }
