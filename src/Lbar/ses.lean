import Lbar.functor
import laurent_measures.functor
import laurent_measures.aux_lemmas

.

/-!
The short exact sequence
```
0 → ℤ[T⁻¹] → ℳ(S, ℤ((T))_r') → ℳ-bar(S)_r' → 0
```
-/

noncomputable theory

open aux_thm69
open_locale nnreal

variables (r' : ℝ≥0) [fact (0 < r')] (S : Fintype)

-- move me
lemma int.coe_nat_injective : function.injective (coe : ℕ → ℤ) :=
λ m n h, int.coe_nat_inj h

namespace laurent_measures

@[simps] def to_Lbar (F : laurent_measures r' S) : Lbar r' S :=
{ to_fun := λ s n, if n = 0 then 0 else F s n,
  coeff_zero' := λ s, if_pos rfl,
  summable' := λ s, begin
    have := nnreal.summable_comp_injective (F.nnreal_summable s) int.coe_nat_injective,
    refine nnreal.summable_of_le _ this,
    intros n,
    split_ifs,
    { simp only [int.nat_abs_zero, nat.cast_zero, zero_mul, zero_le'] },
    { simp only [function.comp_app, nnreal.coe_nat_abs, zpow_coe_nat] }
  end }

lemma to_Lbar_surjective : function.surjective (to_Lbar r' S) :=
begin
  intro G,
  refine ⟨⟨λ s n, G s n.to_nat, λ s, _⟩, _⟩,
  { refine (nnreal.summable_iff_on_nat_less 0 (λ n n0, _)).mpr _,
    { simp [int.to_nat_of_nonpos n0.le] },
    { simpa only [← nnreal.coe_nat_abs] using G.summable' s } },
  { ext s (_|n),
    { exact (G.coeff_zero s).symm },
    { show ite (n.succ = 0) 0 (G s (n + 1)) = G s n.succ, from if_neg n.succ_ne_zero } }
end

lemma nnnorm_to_Lbar (F : laurent_measures r' S) : ∥to_Lbar r' S F∥₊ ≤ ∥F∥₊ :=
begin
  rw [nnnorm_def, Lbar.nnnorm_def],
  refine finset.sum_le_sum (λ s hs, _),
  have := nnreal.summable_comp_injective (F.nnreal_summable s) int.coe_nat_injective,
  refine (tsum_le_tsum _ ((to_Lbar r' S F).summable s) this).trans
    (nnreal.tsum_comp_le_tsum_of_inj (F.nnreal_summable s) int.coe_nat_injective),
  intro n,
  simp only [nnreal.coe_nat_abs, to_Lbar_to_fun, function.comp_app, zpow_coe_nat],
  split_ifs, { rw [nnnorm_zero, zero_mul], exact zero_le' }, { refl }
end

@[simps] def to_Lbar_hom : comphaus_filtered_pseudo_normed_group_with_Tinv_hom r'
  (laurent_measures r' S) (Lbar r' S) :=
{ to_fun := to_Lbar r' S,
  map_zero' := by { ext,
    simp only [to_Lbar_to_fun, zero_apply, if_t_t, Lbar.coe_zero, pi.zero_apply], },
  map_add' := λ F G, by { ext, simp only [to_Lbar_to_fun, add_apply, Lbar.coe_add, pi.add_apply],
    split_ifs, { rw add_zero }, { refl } },
  strict' := λ c F (hF : ∥F∥₊ ≤ c), (nnnorm_to_Lbar r' S F).trans hF,
  continuous' := λ c, begin
    let f : _ := _, show continuous f,
    rw Lbar_le.continuous_iff,
    intros N,
    let e : ℕ ↪ ℤ := ⟨coe, int.coe_nat_injective⟩,
    let T : finset ℤ := (finset.range (N + 1)).map e,
    let g : laurent_measures_bdd r' S T c → Lbar_bdd r' ⟨S⟩ c N := λ F,
    { to_fun := λ s n, if n = 0 then 0 else F s ⟨n, _⟩,
      coeff_zero' := λ s, if_pos rfl,
      sum_le' := _ },
    have : Lbar_le.truncate N ∘ f = g ∘ truncate T,
    { dsimp [f], ext F s ⟨(_|n), hn⟩, { simp only [fin.mk_zero, Lbar_bdd.coeff_zero], },
      simp only [Lbar_le.truncate_to_fun, Lbar_bdd.coe_mk, coe_coe, int.coe_nat_succ,
        truncate_to_fun, subtype.coe_mk, subtype.ext_iff, fin.coe_zero, nat.succ_ne_zero, if_false],
      exact to_Lbar_to_fun r' S F s (n+1), },
    { rw this, exact continuous_of_discrete_topology.comp (truncate_continuous _ _ _ _) },
    { simpa only [coe_coe, finset.mem_map, finset.mem_range, function.embedding.coe_fn_mk,
        int.coe_nat_inj', exists_prop, exists_eq_right] using n.2, },
    { cases S, refine le_trans (finset.sum_le_sum _) F.bound, dsimp,
      rintro s -,
      erw [finset.sum_attach', finset.sum_map, ← fin.sum_univ_eq_sum_range],
      refine finset.sum_le_sum (λ i hi, _),
      simp only [finset.mem_map, finset.mem_range, exists_prop, exists_eq_right, nnreal.coe_nat_abs,
        embedding_like.apply_eq_iff_eq, function.embedding.coe_fn_mk, subtype.coe_mk, zpow_coe_nat],
      rw dif_pos, swap, { exact i.2 },
      split_ifs, { rw [nnnorm_zero, zero_mul], exact zero_le' }, { refl } }
  end,
  map_Tinv' := λ F, begin
    erw [Tinv_apply, Lbar.Tinv_apply],
    ext s (_|n),
    { simp only [to_Lbar_to_fun, eq_self_iff_true, if_true, Lbar.Tinv_zero], },
    { simp only [to_Lbar_to_fun, nat.succ_ne_zero, int.coe_nat_succ, shift_to_fun_to_fun,
        Lbar.Tinv_succ], }
  end }

@[simps]
def to_Lbar_fintype_nattrans : laurent_measures.fintype_functor r' ⟶ Lbar.fintype_functor r' :=
{ app := λ S, to_Lbar_hom r' S,
  naturality' := λ S₁ S₂ f, begin
    ext,
    simp only [fintype_functor_map, category_theory.comp_apply, to_Lbar_hom_to_fun, to_Lbar_to_fun,
      Lbar.fintype_functor_map_to_fun, Lbar.map_to_fun, map_hom, map_apply,
      comphaus_filtered_pseudo_normed_group_with_Tinv_hom.coe_mk],
    split_ifs, { simp only [finset.sum_const_zero], }, { refl }
  end }

@[simps]
def to_Lbar_nattrans : laurent_measures.functor r' ⟶ Lbar.functor r' :=
Profinite.extend_nat_trans $ to_Lbar_fintype_nattrans r'

end laurent_measures
