import tactic.find_unused
import challenge

open tactic

meta def file_list : list (option string) :=
["backup/delta_functor.lean", "backup/extr.lean",
"backup/extr_backup.lean", "backup/multilinear.lean",
"backup/prepresentation.lean", "backup/sheafification_mono.lean",
"scripts/lean_version.lean", "scripts/lint_project.lean",
"scripts/print_lte_axioms.lean", "scripts/print_thm95_axioms.lean",
"src/Lbar/Lbar_le.lean", "src/Lbar/basic.lean", "src/Lbar/bounded.lean",
"src/Lbar/ext.lean", "src/Lbar/ext_aux1.lean", "src/Lbar/ext_aux2.lean",
"src/Lbar/ext_aux3.lean", "src/Lbar/ext_aux4.lean",
"src/Lbar/ext_preamble.lean", "src/Lbar/finsupp_instance.lean",
"src/Lbar/functor.lean", "src/Lbar/iota.lean",
"src/Lbar/kernel_truncate.lean", "src/Lbar/nnnorm_add_class.lean",
"src/Lbar/pseudo_normed_group.lean", "src/Lbar/ses.lean",
"src/Lbar/squares.lean", "src/Lbar/sum_nnnorm.lean",
"src/Lbar/torsion_free_condensed.lean",
"src/Lbar/torsion_free_profinite.lean",
"src/banach.lean", "src/breen_deligne/apply_Pow.lean",
"src/breen_deligne/category.lean", "src/breen_deligne/constants.lean",
"src/breen_deligne/eg.lean", "src/breen_deligne/eval.lean",
"src/breen_deligne/eval1half.lean", "src/breen_deligne/eval2.lean",
"src/breen_deligne/eval_Pow_functor_nat_trans_compatibility.lean",
"src/breen_deligne/functorial_map.lean",
"src/breen_deligne/homotopy.lean", "src/breen_deligne/main.lean",
"src/breen_deligne/suitable.lean", "src/breen_deligne/universal_map.lean",
"src/challenge.lean", "src/challenge_notations.lean",
"src/challenge_prerequisites.lean",
"src/combinatorial_lemma/default.lean",
"src/combinatorial_lemma/finite.lean",
"src/combinatorial_lemma/lem97.lean",
"src/combinatorial_lemma/partition.lean",
"src/combinatorial_lemma/profinite.lean",
"src/combinatorial_lemma/profinite_setup.lean",
"src/condensed/Qprime_isoms.lean", "src/condensed/Qprime_isoms2.lean",
"src/condensed/ab.lean", "src/condensed/ab4.lean",
"src/condensed/ab5.lean", "src/condensed/acyclic.lean",
"src/condensed/adjunctions.lean", "src/condensed/adjunctions2.lean",
"src/condensed/adjunctions_module.lean", "src/condensed/basic.lean",
"src/condensed/bd_lemma.lean", "src/condensed/bd_ses.lean",
"src/condensed/bd_ses_aux.lean", "src/condensed/condensify.lean",
"src/condensed/coproducts.lean", "src/condensed/evaluation_homology.lean",
"src/condensed/exact.lean", "src/condensed/extr/basic.lean",
"src/condensed/extr/equivalence.lean",
"src/condensed/extr/lift_comphaus.lean",
"src/condensed/filtered_colimits.lean",
"src/condensed/filtered_colimits_commute_with_finite_limits.lean",
"src/condensed/is_iso_iff_extrdisc.lean",
"src/condensed/is_proetale_sheaf.lean",
"src/condensed/kernel_comparison.lean",
"src/condensed/proetale_site.lean",
"src/condensed/projective_resolution.lean",
"src/condensed/projective_resolution_module.lean",
"src/condensed/rescale.lean",
"src/condensed/sheafification_homology.lean",
"src/condensed/sheafification_mono.lean",
"src/condensed/short_exact.lean", "src/condensed/tensor.lean",
"src/condensed/tensor_short_exact.lean",
"src/condensed/top_comparison.lean", "src/examples/pBanach.lean",
"src/examples/real.lean", "src/facts/default.lean",
"src/facts/int.lean", "src/facts/nnreal.lean",
"src/facts/normed_group.lean", "src/for_mathlib/AddCommGroup.lean",
"src/for_mathlib/AddCommGroup/ab4.lean",
"src/for_mathlib/AddCommGroup/direct_sum_colimit.lean",
"src/for_mathlib/AddCommGroup/epi.lean",
"src/for_mathlib/AddCommGroup/exact.lean",
"src/for_mathlib/AddCommGroup/explicit_limits.lean",
"src/for_mathlib/AddCommGroup/explicit_products.lean",
"src/for_mathlib/AddCommGroup/kernels.lean",
"src/for_mathlib/AddCommGroup/pt.lean",
"src/for_mathlib/AddCommGroup/tensor.lean",
"src/for_mathlib/AddCommGroup/tensor_short_exact.lean",
"src/for_mathlib/AddCommGroup_instances.lean",
"src/for_mathlib/Cech/adjunction.lean",
"src/for_mathlib/Cech/homotopy.lean",
"src/for_mathlib/Cech/split.lean", "src/for_mathlib/CompHaus.lean",
"src/for_mathlib/Ext_quasi_iso.lean", "src/for_mathlib/Fintype.lean",
"src/for_mathlib/FreeAb.lean", "src/for_mathlib/Gordan.lean",
"src/for_mathlib/Profinite/arrow_limit.lean",
"src/for_mathlib/Profinite/clopen_limit.lean",
"src/for_mathlib/Profinite/compat_discrete_quotient.lean",
"src/for_mathlib/Profinite/disjoint_union.lean",
"src/for_mathlib/Profinite/extend.lean",
"src/for_mathlib/Profinite/product.lean",
"src/for_mathlib/Profinite/quotient_map.lean",
"src/for_mathlib/SemiNormedGroup.lean",
"src/for_mathlib/SemiNormedGroup_ulift.lean",
"src/for_mathlib/SheafOfTypes_sheafification.lean",
"src/for_mathlib/ab4.lean", "src/for_mathlib/ab5.lean",
"src/for_mathlib/ab52.lean", "src/for_mathlib/abelian_category.lean",
"src/for_mathlib/abelian_group_object.lean",
"src/for_mathlib/abelian_sheaves/exact.lean",
"src/for_mathlib/abelian_sheaves/functor_category.lean",
"src/for_mathlib/abelian_sheaves/main.lean",
"src/for_mathlib/acyclic.lean", "src/for_mathlib/additive_functor.lean",
"src/for_mathlib/arrow/split.lean",
"src/for_mathlib/arrow_preadditive.lean",
"src/for_mathlib/bicartesian.lean", "src/for_mathlib/bicartesian2.lean",
"src/for_mathlib/bicartesian3.lean", "src/for_mathlib/bicartesian4.lean",
"src/for_mathlib/cech.lean", "src/for_mathlib/chain_complex_cons.lean",
"src/for_mathlib/chain_complex_exact.lean",
"src/for_mathlib/colim_preserves_colimits.lean",
"src/for_mathlib/commsq.lean", "src/for_mathlib/complex_extend.lean",
"src/for_mathlib/composable_morphisms.lean",
"src/for_mathlib/concrete_equalizer.lean",
"src/for_mathlib/coprod_op.lean",
"src/for_mathlib/derived/Ext_lemmas.lean",
"src/for_mathlib/derived/K_projective.lean",
"src/for_mathlib/derived/ProjectiveResolution.lean",
"src/for_mathlib/derived/bounded_homotopy_category.lean",
"src/for_mathlib/derived/defs.lean",
"src/for_mathlib/derived/derived_cat.lean",
"src/for_mathlib/derived/example.lean",
"src/for_mathlib/derived/ext_coproducts.lean",
"src/for_mathlib/derived/homological.lean",
"src/for_mathlib/derived/lemmas.lean", "src/for_mathlib/derived/les.lean",
"src/for_mathlib/derived/les2.lean", "src/for_mathlib/derived/les3.lean",
"src/for_mathlib/derived/les_facts.lean",
"src/for_mathlib/derived_functor.lean",
"src/for_mathlib/derived_functor_zero.lean",
"src/for_mathlib/embed_preserves_colimits.lean",
"src/for_mathlib/endomorphisms/Ext.lean",
"src/for_mathlib/endomorphisms/ab4.lean",
"src/for_mathlib/endomorphisms/basic.lean",
"src/for_mathlib/endomorphisms/functor.lean",
"src/for_mathlib/endomorphisms/homology.lean",
"src/for_mathlib/ennreal.lean", "src/for_mathlib/equalizers.lean",
"src/for_mathlib/equivalence_additive.lean",
"src/for_mathlib/exact_filtered_colimits.lean",
"src/for_mathlib/exact_functor.lean",
"src/for_mathlib/exact_lift_desc.lean",
"src/for_mathlib/exact_seq.lean", "src/for_mathlib/exact_seq2.lean",
"src/for_mathlib/exact_seq3.lean", "src/for_mathlib/exact_seq4.lean",
"src/for_mathlib/ext.lean", "src/for_mathlib/fin_functor.lean",
"src/for_mathlib/fintype_induction.lean",
"src/for_mathlib/free_abelian_exact.lean",
"src/for_mathlib/free_abelian_group.lean",
"src/for_mathlib/free_abelian_group2.lean",
"src/for_mathlib/has_homology.lean",
"src/for_mathlib/has_homology_aux.lean",
"src/for_mathlib/hom_single_iso.lean",
"src/for_mathlib/hom_single_iso2.lean",
"src/for_mathlib/homological_complex.lean",
"src/for_mathlib/homological_complex2.lean",
"src/for_mathlib/homological_complex_abelian.lean",
"src/for_mathlib/homological_complex_equiv_functor_category.lean",
"src/for_mathlib/homological_complex_map_d_to_d_from.lean",
"src/for_mathlib/homological_complex_op.lean",
"src/for_mathlib/homological_complex_shift.lean",
"src/for_mathlib/homology.lean", "src/for_mathlib/homology_exact.lean",
"src/for_mathlib/homology_iso.lean",
"src/for_mathlib/homology_iso_Ab.lean",
"src/for_mathlib/homology_iso_datum.lean",
"src/for_mathlib/homology_lift_desc.lean",
"src/for_mathlib/homology_map.lean",
"src/for_mathlib/homology_map_datum.lean",
"src/for_mathlib/homotopy_category.lean",
"src/for_mathlib/homotopy_category_coproducts.lean",
"src/for_mathlib/homotopy_category_functor_compatibilities.lean",
"src/for_mathlib/homotopy_category_lemmas.lean",
"src/for_mathlib/homotopy_category_op.lean",
"src/for_mathlib/homotopy_category_pretriangulated.lean",
"src/for_mathlib/horseshoe.lean", "src/for_mathlib/imker.lean",
"src/for_mathlib/int.lean", "src/for_mathlib/internal_hom.lean",
"src/for_mathlib/is_biprod.lean", "src/for_mathlib/is_iso_iota.lean",
"src/for_mathlib/is_iso_neg.lean",
"src/for_mathlib/is_locally_constant.lean",
"src/for_mathlib/is_quasi_iso.lean",
"src/for_mathlib/is_quasi_iso_sigma.lean",
"src/for_mathlib/kernel_comparison.lean",
"src/for_mathlib/les_homology.lean", "src/for_mathlib/logic.lean",
"src/for_mathlib/map_to_sheaf_is_iso.lean",
"src/for_mathlib/mapping_cone.lean", "src/for_mathlib/module_epi.lean",
"src/for_mathlib/monoidal_category.lean",
"src/for_mathlib/nat_iso_map_homological_complex.lean",
"src/for_mathlib/nat_trans.lean", "src/for_mathlib/neg_one_pow.lean",
"src/for_mathlib/nnrat.lean", "src/for_mathlib/nnreal.lean",
"src/for_mathlib/nnreal_int_binary.lean",
"src/for_mathlib/nnreal_nat_binary.lean",
"src/for_mathlib/nnreal_to_nat_colimit.lean", "src/for_mathlib/op.lean",
"src/for_mathlib/order.lean", "src/for_mathlib/pi_induced.lean",
"src/for_mathlib/pid.lean", "src/for_mathlib/pow_functor.lean",
"src/for_mathlib/preadditive_yoneda.lean",
"src/for_mathlib/preserves_exact.lean",
"src/for_mathlib/preserves_finite_limits.lean",
"src/for_mathlib/preserves_limits.lean",
"src/for_mathlib/presieve.lean", "src/for_mathlib/product_op.lean",
"src/for_mathlib/projective_replacement.lean",
"src/for_mathlib/projectives.lean", "src/for_mathlib/pullbacks.lean",
"src/for_mathlib/quotient_map.lean",
"src/for_mathlib/random_homological_lemmas.lean",
"src/for_mathlib/rational_cones.lean", "src/for_mathlib/real.lean",
"src/for_mathlib/salamander.lean", "src/for_mathlib/sheaf.lean",
"src/for_mathlib/sheafification_equiv_compatibility.lean",
"src/for_mathlib/sheafification_mono.lean",
"src/for_mathlib/short_complex.lean",
"src/for_mathlib/short_complex_colimits.lean",
"src/for_mathlib/short_complex_functor_category.lean",
"src/for_mathlib/short_complex_homological_complex.lean",
"src/for_mathlib/short_complex_projections.lean",
"src/for_mathlib/short_exact.lean",
"src/for_mathlib/short_exact_sequence.lean",
"src/for_mathlib/simplicial/complex.lean",
"src/for_mathlib/simplicial/iso.lean",
"src/for_mathlib/single_coproducts.lean",
"src/for_mathlib/snake_lemma.lean", "src/for_mathlib/snake_lemma2.lean",
"src/for_mathlib/snake_lemma3.lean",
"src/for_mathlib/snake_lemma_naturality.lean",
"src/for_mathlib/snake_lemma_naturality2.lean",
"src/for_mathlib/split_exact.lean", "src/for_mathlib/sum_str.lean",
"src/for_mathlib/topology.lean", "src/for_mathlib/triangle.lean",
"src/for_mathlib/triangle_shift.lean", "src/for_mathlib/truncation.lean",
"src/for_mathlib/truncation_Ext.lean", "src/for_mathlib/tsum.lean",
"src/for_mathlib/two_step_resolution.lean",
"src/for_mathlib/types.lean", "src/for_mathlib/unflip.lean",
"src/for_mathlib/universal_delta_functor/basic.lean",
"src/for_mathlib/unop.lean", "src/for_mathlib/whisker_adjunction.lean",
"src/for_mathlib/wide_pullback_iso.lean",
"src/for_mathlib/yoneda.lean", "src/for_mathlib/yoneda_left_exact.lean",
"src/free_pfpng/acyclic.lean", "src/free_pfpng/basic.lean",
"src/free_pfpng/epi.lean", "src/free_pfpng/lemmas.lean",
"src/free_pfpng/main.lean", "src/free_pfpng/mono.lean",
"src/free_pfpng/setup.lean", "src/hacks_and_tricks/asyncI.lean",
"src/hacks_and_tricks/by_exactI_hack.lean",
"src/hacks_and_tricks/type_pow.lean",
"src/invpoly/basic.lean", "src/invpoly/functor.lean",
"src/invpoly/ses.lean", "src/laurent_measures/aux_lemmas.lean",
"src/laurent_measures/basic.lean", "src/laurent_measures/bounded.lean",
"src/laurent_measures/condensed.lean", "src/laurent_measures/ext.lean",
"src/laurent_measures/functor.lean",
"src/laurent_measures/int_nat_shifts.lean",
"src/laurent_measures/no_longer_needed_maybe.lean",
"src/laurent_measures/prop72.lean",
"src/laurent_measures/ses.lean", "src/laurent_measures/ses2.lean",
"src/laurent_measures/simpler_laurent_measures.lean",
"src/laurent_measures/theta.lean", "src/laurent_measures/thm69.lean",
"src/liquid.lean", "src/locally_constant/SemiNormedGroup.lean",
"src/locally_constant/Vhat.lean", "src/locally_constant/analysis.lean",
"src/locally_constant/completion.lean",
"src/locally_constant/completion_aux.lean",
"src/normed_free_pfpng/basic.lean", "src/normed_free_pfpng/compare.lean",
"src/normed_group/controlled_exactness.lean",
"src/normed_group/normed_with_aut.lean",
"src/normed_group/pseudo_normed_group.lean", "src/normed_snake.lean",
"src/normed_snake_dual.lean", "src/normed_spectral.lean",
"src/polyhedral_lattice/Hom.lean", "src/polyhedral_lattice/basic.lean",
"src/polyhedral_lattice/category.lean",
"src/polyhedral_lattice/cech.lean",
"src/polyhedral_lattice/cosimplicial.lean",
"src/polyhedral_lattice/cosimplicial_extra.lean",
"src/polyhedral_lattice/finsupp.lean", "src/polyhedral_lattice/int.lean",
"src/polyhedral_lattice/pseudo_normed_group.lean",
"src/polyhedral_lattice/quotient.lean",
"src/polyhedral_lattice/topology.lean",
"src/prop819.lean", "src/prop819/completion.lean",
"src/prop819/strict_complex_iso.lean", "src/prop_92/concrete.lean",
"src/prop_92/extension_profinite.lean", "src/prop_92/prop_92.lean",
"src/pseudo_normed_group/CLC.lean", "src/pseudo_normed_group/FP.lean",
"src/pseudo_normed_group/FP2.lean", "src/pseudo_normed_group/LC.lean",
"src/pseudo_normed_group/QprimeFP.lean",
"src/pseudo_normed_group/Tinv.lean", "src/pseudo_normed_group/basic.lean",
"src/pseudo_normed_group/bounded_limits.lean",
"src/pseudo_normed_group/breen_deligne.lean",
"src/pseudo_normed_group/category/CompHausFiltPseuNormGrp.lean",
"src/pseudo_normed_group/category/CompHausFiltPseuNormGrpWithTinv.lean",
"src/pseudo_normed_group/category/ProFiltPseuNormGrp.lean",
"src/pseudo_normed_group/category/ProFiltPseuNormGrpWithTinv.lean",
"src/pseudo_normed_group/category/default.lean",
"src/pseudo_normed_group/category/strictCompHausFiltPseuNormGrp.lean",
"src/pseudo_normed_group/category/strictProFiltPseuNormGrp.lean",
"src/pseudo_normed_group/category/strictProFiltPseuNormGrpWithTinv.lean",
"src/pseudo_normed_group/homotopy.lean",
"src/pseudo_normed_group/profinitely_filtered.lean",
"src/pseudo_normed_group/splittable.lean",
"src/pseudo_normed_group/sum_hom.lean",
"src/pseudo_normed_group/system_of_complexes.lean",
"src/pseudo_normed_group/system_of_complexes2.lean",
"src/pseudo_normed_group/with_Tinv.lean", "src/real_measures/basic.lean",
"src/real_measures/condensed.lean", "src/real_measures/default.lean",
"src/rescale/CLC.lean", "src/rescale/FiltrationPow.lean",
"src/rescale/LC.lean", "src/rescale/Tinv.lean", "src/rescale/basic.lean",
"src/rescale/normed_group.lean", "src/rescale/polyhedral_lattice.lean",
"src/rescale/pseudo_normed_group.lean",
"src/statement.lean", "src/system_of_complexes/basic.lean",
"src/system_of_complexes/completion.lean",
"src/system_of_complexes/double.lean",
"src/system_of_complexes/rescale.lean",
"src/system_of_complexes/shift_sub_id.lean",
"src/system_of_complexes/truncate.lean", "src/thm95/col_exact.lean",
"src/thm95/col_exact_prep.lean", "src/thm95/constants/default.lean",
"src/thm95/constants/spectral_constants.lean", "src/thm95/default.lean",
"src/thm95/double_complex.lean", "src/thm95/homotopy.lean",
"src/thm95/modify_complex.lean", "src/thm95/pfpng_iso.lean",
"src/thm95/polyhedral_iso.lean", "src/thm95/row_iso.lean"]

open tactic

meta def unused_defs (fs : list (option string)) : tactic unit :=
do ds ← all_unused fs,
let ds := ds.filter (λ t, declaration.is_definition t),
let ds' := (ds.to_list.map $ λ ⟨n,_⟩, n.to_string),
let ds'' := string.intercalate "\n" ds',
tactic.trace ds''


attribute [main_declaration] liquid_tensor_experiment
attribute [main_declaration] AddCommGroup.Ext_zmod

-- run_cmd unused_defs file_list
