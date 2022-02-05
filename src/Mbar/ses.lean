import Mbar.functor
import laurent_measures.functor

.

/-!
The short exact sequence
```
0 → ℤ[T⁻¹] → ℳ(S, ℤ((T))_r') → ℳ-bar(S)_r' → 0
```
-/

noncomputable theory

open_locale nnreal

variables (r' : ℝ≥0) [fact (0 < r')] (S : Fintype)

-- move me
lemma int.coe_nat_injective : function.injective (coe : ℕ → ℤ) :=
λ m n h, int.coe_nat_inj h

namespace laurent_measures

@[simps] def to_Mbar (F : laurent_measures r' S) : Mbar r' S :=
{ to_fun := λ s n, if n = 0 then 0 else F s n,
  coeff_zero' := λ s, if_pos rfl,
  summable' := λ s, begin
    have := nnreal.summable_comp_injective (F.nnreal_summable s) int.coe_nat_injective,
    refine nnreal.summable_of_le _ this,
    intros n,
    simp only [function.comp_app, zpow_coe_nat],
    split_ifs,
    { simp only [int.nat_abs_zero, nat.cast_zero, zero_mul, zero_le'], },
    { simp only [nnreal.coe_nat_abs], }
  end }

lemma to_Mbar_surjective : function.surjective (to_Mbar r' S) :=
begin
  intro G,
  refine ⟨⟨λ s n, G s n.to_nat, λ s, _⟩, _⟩,
  { rw ← int.coe_nat_injective.summable_iff,
    { refine nnreal.summable_of_le _ (G.summable s),
      intro n,
      simp only [nnreal.coe_nat_abs, function.comp_app, int.to_nat_coe_nat, zpow_coe_nat] },
    { rintro (n|n),
      { simp only [int.of_nat_eq_coe, set.mem_range_self, not_true, forall_false_left], },
      { intro, dsimp [int.to_nat], simp only [Mbar.coeff_zero, nnnorm_zero, zero_mul], } } },
  { ext s (_|n), { exact (G.coeff_zero s).symm }, { dsimp, exact if_neg (nat.succ_ne_zero n), } }
end

lemma nnnorm_to_Mbar (F : laurent_measures r' S) : ∥to_Mbar r' S F∥₊ ≤ ∥F∥₊ :=
begin
  rw [nnnorm_def, Mbar.nnnorm_def],
  refine finset.sum_le_sum (λ s hs, _),
  have := nnreal.summable_comp_injective (F.nnreal_summable s) int.coe_nat_injective,
  refine (tsum_le_tsum _ ((to_Mbar r' S F).summable s) this).trans
    (nnreal.tsum_comp_le_tsum_of_inj (F.nnreal_summable s) int.coe_nat_injective),
  intro n,
  simp only [nnreal.coe_nat_abs, to_Mbar_to_fun, function.comp_app, zpow_coe_nat],
  split_ifs, { rw [nnnorm_zero, zero_mul], exact zero_le' }, { refl }
end

@[simps] def to_Mbar_hom : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r'
  (laurent_measures r' S) (Mbar r' S) :=
{ to_fun := to_Mbar r' S,
  map_zero' := by { ext,
    simp only [to_Mbar_to_fun, zero_apply, if_t_t, Mbar.coe_zero, pi.zero_apply], },
  map_add' := λ F G, by { ext, simp only [to_Mbar_to_fun, add_apply, Mbar.coe_add, pi.add_apply],
    split_ifs, { rw add_zero }, { refl } },
  strict' := λ c F (hF : ∥F∥₊ ≤ c), (nnnorm_to_Mbar r' S F).trans hF,
  continuous' := λ c, begin
    let f : _ := _, show continuous f,
    rw Mbar_le.continuous_iff,
    intros N,
    let e : ℕ ↪ ℤ := ⟨coe, int.coe_nat_injective⟩,
    let T : finset ℤ := (finset.range (N + 1)).map e,
    let g : laurent_measures_bdd r' S T c → Mbar_bdd r' ⟨S⟩ c N := λ F,
    { to_fun := λ s n, if n = 0 then 0 else F s ⟨n, _⟩,
      coeff_zero' := λ s, if_pos rfl,
      sum_le' := _ },
    have : Mbar_le.truncate N ∘ f = g ∘ truncate T,
    { dsimp [f], ext F s ⟨(_|n), hn⟩, { simp only [fin.mk_zero, Mbar_bdd.coeff_zero], },
      simp only [Mbar_le.truncate_to_fun, Mbar_bdd.coe_mk, coe_coe, int.coe_nat_succ,
        truncate_to_fun, subtype.coe_mk, subtype.ext_iff, fin.coe_zero, nat.succ_ne_zero, if_false],
      exact to_Mbar_to_fun r' S F s (n+1), },
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
    simp only [Tinv_apply, Mbar.Tinv_apply],
    ext s (_|n),
    { simp only [to_Mbar_to_fun, eq_self_iff_true, if_true, Mbar.Tinv_zero], },
    { simp only [to_Mbar_to_fun, nat.succ_ne_zero, int.coe_nat_succ, shift_to_fun_to_fun,
        Mbar.Tinv_succ], }
  end }

@[simps]
def to_Mbar_fintype_nattrans : laurent_measures.fintype_functor r' ⟶ Mbar.fintype_functor r' :=
{ app := λ S, to_Mbar_hom r' S,
  naturality' := λ S₁ S₂ f, begin
    ext,
    simp only [fintype_functor_map, category_theory.comp_apply, to_Mbar_hom_to_fun, to_Mbar_to_fun,
      Mbar.fintype_functor_map_to_fun, Mbar.map_to_fun, map_hom, map_apply,
      profinitely_filtered_pseudo_normed_group_with_Tinv_hom.coe_mk],
    split_ifs, { simp only [finset.sum_const_zero], }, { refl }
  end }

@[simps]
def to_Mbar_nattrans : laurent_measures.functor r' ⟶ Mbar.functor r' :=
Profinite.extend_nat_trans $ to_Mbar_fintype_nattrans r'

end laurent_measures
