import free_pfpng.main
import for_mathlib.derived.example
.

noncomputable theory

universes u

open category_theory opposite ProFiltPseuNormGrp₁
open_locale nnreal

variables (S : Profinite.{u})
variables (V : Type u) [add_comm_group V] [uniform_space V]
variables [topological_add_group V] [complete_space V]

theorem free_acyclic (i : ℤ) (hi : 0 < i) :
  is_zero (((Ext' i).obj (op ((Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab).obj S))).obj
    (Condensed.of_top_ab V)) :=
begin
  sorry
end

theorem free_pfpng_acyclic (i : ℤ) (hi : 0 < i) :
  is_zero (((Ext' i).obj (op ((condensify (free_pfpng_functor ⋙ to_CHFPNG₁)).obj S))).obj
    (Condensed.of_top_ab V)) :=
begin
  refine is_zero_of_iso_of_zero (free_acyclic S V i hi) _,
  conv { rw ← functor.flip_obj_obj, congr, skip, rw ← functor.flip_obj_obj },
  refine functor.map_iso _ (iso.app _ _).op,
  exact free_pfpng_profinite_iso
end
