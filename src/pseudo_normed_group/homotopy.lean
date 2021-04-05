import pseudo_normed_group.system_of_complexes
import rescale.CLC

.

noncomputable theory

universe variables u

open_locale nnreal

open differential_object.complex_like

variables {BD BD₁ BD₂ : breen_deligne.data} (f g : BD₁ ⟶ BD₂)
variables (h : homotopy f g)

variables (c' c₁' c₂' : ℕ → ℝ≥0)
variables [BD.suitable c'] [BD₁.suitable c₁'] [BD₂.suitable c₂']
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)]
variables (M : ProFiltPseuNormGrpWithTinv.{u} r') (c : ℝ≥0)

namespace breen_deligne

section homotopy

open differential_object differential_object.complex_like

-- def BD_map [∀ i, (f.f i).suitable (c₁' i) (c₂' i)] :
--   BD₂.complex c₂' r V r' M c ⟶ BD₁.complex c₁' r V r' M c :=
-- hom.mk' (λ i, ((f.f i).eval_CLCFPTinv r V r' (c * c₁' i) (c * c₂' i)).app _)
-- begin
--   dsimp [coherent_indices],
--   intros i j hij, subst j,
--   erw [cochain_complex.mk'_d', cochain_complex.mk'_d'],
--   dsimp only [data.complex_d],
--   erw [← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _,
--        ← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _],
--   { congr' 1, have := f.comm (i+1) i, exact this.symm },
--   { exact universal_map.suitable.comp (c * c₁' i) },
--   { exact universal_map.suitable.comp (c * c₂' (i+1)) }
-- end

variables {f g}

-- def homotopy [∀ i, (f.f i).suitable (c₁' i) (c₂' i)] [∀ i, (g.f i).suitable (c₁' i) (c₂' i)]
--   [∀ j i, (h.h j i).suitable (c₁' j) (c₂' i)] :
--   homotopy (BD_map f c₁' c₂' r V M c) (BD_map g c₁' c₂' r V M c) :=
-- { h := λ j i, (h.h i j).eval_CLCFPTinv r V r' M (c * c₁' i) (c * c₂' j),
--   h_eq_zero := λ i j hij,
--   begin
--     convert universal_map.eval_CLCFPTinv_zero r V r' M _ _,
--     rw h.h_eq_zero,
--     exact ne.symm hij
--   end,
--   comm :=
--   begin
--     simp only [htpy_idx_rel₁_tt_nat, htpy_idx_rel₂_tt_nat],
--     rintro i j k rfl,
--     simp only [nat.succ_ne_zero i, nat.succ_eq_add_one, false_and, or_false],
--     rintro rfl,
--     erw [cochain_complex.mk'_d', cochain_complex.mk'_d'],
--     dsimp only [data.complex_d],
--     erw [← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _,
--         ← universal_map.eval_CLCFPTinv_comp r V r' M _ _ _ _ _],
--     swap, { exact universal_map.suitable.comp (c * c₂' (i+1+1)) },
--     swap, { exact universal_map.suitable.comp (c * c₁' i) },
--     sorry
--   end }

end homotopy

section rescale

-- move this
def rescale_constants (c' : ℕ → ℝ≥0) (N : ℝ≥0) : ℕ → ℝ≥0 :=
λ i, (c' i) * N⁻¹

-- warning: this might need `[fact (0 < N)]`
instance rescale_constants_suitable (N : ℝ≥0) :
  BD.suitable (rescale_constants c' N) :=
by { delta rescale_constants, apply_instance }

variables (BD)

open differential_object.complex_like category_theory
open ProFiltPseuNormGrpWithTinv (of)

open normed_group_hom

lemma aux₀ (c c' N : ℝ≥0) : fact (c * c' * N⁻¹ ≤ c * (c' * N⁻¹)) :=
by simpa only [mul_assoc] using nnreal.fact_le_refl _

lemma aux₀' (c c' N : ℝ≥0) : fact (r' * (c * c') * N⁻¹ ≤ r' * (c * (c' * N⁻¹))) :=
by simpa only [mul_assoc] using nnreal.fact_le_refl _

local attribute [instance] aux₀ aux₀'

-- def rescale_hom (c c' N : ℝ≥0) (n : ℕ) :
--   CLCFPTinv r V r' M (c * (c' * N⁻¹)) n ⟶ CLCFPTinv r V r' (rescale N M) (c * c') n :=
-- equalizer.map (CLCFP.res V r' _ _ _) (CLCFP.res V r' _ _ _)
-- sorry
-- begin
--   sorry
-- end

def foo (a b : ℕ → ℝ≥0) [∀ i, fact (a i ≤ r' * b i)] [∀ i, fact (a i ≤ b i)] (i) :=
(CLCFPTinv₂ r V r' (b i) (a i) (BD.X i)).obj (opposite.op M)

def foo_d (a b : ℕ → ℝ≥0) [∀ i, fact (a i ≤ r' * b i)] [∀ i, fact (a i ≤ b i)]
  (_ :∀ i j, universal_map.suitable (a j) (a i) (BD.d j i))
  (_ :∀ i j, universal_map.suitable (b j) (b i) (BD.d j i))
  (i j) :
  foo BD r V M a b i ⟶ foo BD r V M a b j :=
(universal_map.eval_CLCFPTinv₂ r V r' (b i) (a i) (b j) (a j) (BD.d j i)).app
  (opposite.op M)

def cochain_complex.mk (X d d_comp_d d_eq_zero) : cochain_complex ℕ NormedGroup :=
{ X := X,
  d := d,
  d_comp_d := d_comp_d,
  d_eq_zero := d_eq_zero }

def bar (a b : ℕ → ℝ≥0) [∀ i, fact (a i ≤ r' * b i)] [∀ i, fact (a i ≤ b i)]
  (_ : ∀ i j, universal_map.suitable (a j) (a i) (BD.d j i))
  (_ : ∀ i j, universal_map.suitable (b j) (b i) (BD.d j i))
  (h1 h2) : cochain_complex ℕ NormedGroup :=
cochain_complex.mk (foo BD r V M a b)
  (foo_d BD r V M a b (by apply_instance) (by apply_instance))
  h1 h2

open opposite

-- this is not `iso.refl` -- so close, and yet so far away
-- the difference is `M_{(c * c_i) * N⁻¹}` vs `M_{c * (c_i * N⁻¹)}`
def complex_rescale_iso_X (N : ℝ≥0) (i : ℕ) :
  ((BD.complex (rescale_constants c' N) r V r' c).obj (op M)).X i ≅
  ((BD.complex c' r V r' c).obj (op $ of r' $ rescale N M)).X i :=
eq_to_iso $ begin
  dsimp only [data.complex, data.complex₂, data.complex₂_X, CLCFPTinv₂, rescale_constants],
  change foo BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) i =
         foo BD r V M (λ i, r' * (c * c' i) * N⁻¹) (λ i, c * c' i * N⁻¹) i,
  simp only [mul_assoc],
end

-- set_option pp.notation false
-- set_option pp.implicit true
-- #print foo_d
-- this is not `iso.refl` -- so close, and yet so far away
-- the difference is `M_{(c * c_i) * N⁻¹}` vs `M_{c * (c_i * N⁻¹)}`
def complex_rescale_iso (N : ℝ≥0) :
  (BD.complex (rescale_constants c' N) r V r' c).obj (op M) ≅
  (BD.complex c' r V r' c).obj (op $ of r' $ rescale N M) :=
eq_to_iso $ begin
  dsimp only [data.complex, rescale_constants],
  transitivity
    (BD.complex₂ r V r' (λ (i : ℕ), c * c' i * N⁻¹) (λ (i : ℕ), r' * (c * c' i) * N⁻¹)).obj (op $ of r' M),
  { simp only [mul_assoc, ProFiltPseuNormGrpWithTinv.of_coe] },
  dsimp only [data.complex₂, rescale_constants],
  ext i,
  { refl },
  { dsimp only [data.complex₂_d, universal_map.eval_CLCFPTinv₂, _root_.id,
      NormedGroup.equalizer.map_nat_app],
    apply heq_of_eq,
    ext i j : 2,
    simp only [universal_map.eval_CLCFP_rescale V r' (c * c' i) (c * c' j) _ _ (BD.d j i) N M,
      universal_map.eval_CLCFP_rescale V r' (r' * (c * c' i)) (r' * (c * c' j)) _ _ (BD.d j i) N M],
    refl, refl,
     },
end.
  dsimp only [data.complex, data.complex₂, -- data.complex_X, data.complex_d, CLCFPTinv,
    universal_map.eval_CLCFPTinv, rescale_constants],
  -- letI : ∀ (i j : ℕ), (BD.d j i).suitable (r' * (c * (c' j * N⁻¹))) (r' * (c * (c' i * N⁻¹))) := _,
  -- letI : ∀ (i j : ℕ), (BD.d j i).suitable (c * (c' j * N⁻¹)) (c * (c' i * N⁻¹)) := _,
  -- letI : ∀ (i j : ℕ), (BD.d j i).suitable (r' * (c * c' j) * N⁻¹) (r' * (c * c' i) * N⁻¹) := _,
  -- letI : ∀ (i j : ℕ), (BD.d j i).suitable (c * c' j * N⁻¹) (c * c' i * N⁻¹) := _,
  -- transitivity,
  -- suffices : bar BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) _ _ _ _ = _,
  -- { exact this },
  simp only [mul_assoc],

end.
  have : ∀ i j,
    (CLCFPTinv₂ r V r' (c * (c' i * N⁻¹)) (r' * (c * (c' i * N⁻¹))) (BD.X i)).obj (opposite.op M) =
    foo BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) i := λ _ _, rfl,

  change @eq
    (∀ (i j : ℕ),
      foo BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) i  ⟶
      (CLCFPTinv₂ r V r' (c * (c' j * N⁻¹)) (r' * (c * (c' j * N⁻¹))) (BD.X j)).obj (opposite.op M))
    (λ (i j : ℕ),
      (universal_map.eval_CLCFPTinv₂ r V r' (c * (c' i * N⁻¹)) (r' * (c * (c' i * N⁻¹))) (c * (c' j * N⁻¹))
        (r' * (c * (c' j * N⁻¹)))
        (BD.d j i)).app
        (opposite.op M)) _,

  -- change foo_d BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) _ _ == _,

  change
    -- bar BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) _ _ =
    -- bar BD r V M (λ i, r' * (c * c' i) * N⁻¹) (λ i, c * c' i * N⁻¹) _
    _,

end.
  -- dsimp only [data.complex, data.complex_X, complex_rescale_iso_X, data.complex_d,
  --   CLCFPTinv, universal_map.eval_CLCFPTinv, CLCFPTinv₂, rescale_constants,
  --   CLCPTinv.F_obj],
  -- change (_ ≫ _ : foo BD r V M _ _ i ⟶ foo BD r V M _ _ j) =
  --       _ --  foo BD r V M (λ i, r' * (c * c' i) * N⁻¹) (λ i, c * c' i * N⁻¹) i
  --        ,

  generalize_proofs,
  -- ext i,
  { dsimp only [data.complex, data.complex_X, CLCFPTinv, CLCFPTinv₂, rescale_constants,
      CLCPTinv.F_obj],
    change foo BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) i =
           foo BD r V M (λ i, r' * (c * c' i) * N⁻¹) (λ i, c * c' i * N⁻¹) i,
    simp only [mul_assoc] },
  dsimp only [data.complex, data.complex_X, data.complex_d,
    CLCFPTinv, universal_map.eval_CLCFPTinv, CLCFPTinv₂, rescale_constants,
    CLCPTinv.F_obj],
  -- letI : ∀ (i j : ℕ), (BD.d j i).suitable (r' * (c * (c' j * N⁻¹))) (r' * (c * (c' i * N⁻¹))) := _,
  -- letI : ∀ (i j : ℕ), (BD.d j i).suitable (c * (c' j * N⁻¹)) (c * (c' i * N⁻¹)) := _,
  -- letI : ∀ (i j : ℕ), (BD.d j i).suitable (r' * (c * c' j) * N⁻¹) (r' * (c * c' i) * N⁻¹) := _,
  -- letI : ∀ (i j : ℕ), (BD.d j i).suitable (c * c' j * N⁻¹) (c * c' i * N⁻¹) := _,
  -- change foo_d BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) _ _ ==
  --        foo_d BD r V M (λ i, r' * (c * c' i) * N⁻¹) (λ i, c * c' i * N⁻¹) _ _,
  change @heq (∀ i j, foo BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) i ⟶
     foo BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) j) _ _ _,
  -- change foo_d BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) _ _ == _,
  -- suffices h1, suffices h2,
end.
  change
  @eq (@cochain_complex.{(max u u_1)+1 (max u u_1)} nat NormedGroup.{(max u u_1)} nat.has_succ
       NormedGroup.large_category.{(max u u_1)}
       NormedGroup.category_theory.limits.has_zero_morphisms.{(max u u_1)})
  (@differential_object.complex_like.mk _ _ _ _ _ _ _ _ _ _) _,

    -- _,
    -- -- foo BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)),
    -- d := _,
    -- d_comp_d := _,
    -- d_eq_zero := _ }
    -- _,
  --   -- bar BD r V M (λ i, r' * (c * (c' i * N⁻¹))) (λ i, c * (c' i * N⁻¹)) _
  --       --  bar BD r V M (λ i, r' * (c * c' i) * N⁻¹) (λ i, c * c' i * N⁻¹) _
  --        _,
  -- simp only [mul_assoc],
  sorry
end

variable (N : ℝ≥0)
open pseudo_normed_group

set_option pp.implicit true
example : (filtration (rescale N M) c : Type*) = filtration M (c * N⁻¹) := rfl
theorem foo (n) : CLCFP V r' (rescale N M) c n = CLCFP V r' M (c * N⁻¹) n := rfl
theorem bar (n) :
  (CLCFP.Tinv V r' c n : CLCFP V r' (rescale N M) c n ⟶ CLCFP V r' M (r' * c * N⁻¹) n) =
  ((CLCFP.Tinv V r' (c * N⁻¹) n : CLCFP V r' M (c * N⁻¹) n ⟶ CLCFP V r' M (r' * (c * N⁻¹)) n) ≫
    (CLCFP.res _ _ _ _ _ : CLCFP V r' M (r' * (c * N⁻¹)) n ⟶ CLCFP V r' M (r' * c * N⁻¹) n)) :=
begin
  dsimp [CLCFP.Tinv_def],
  have := (CLCFP.Tinv'_of_hom V r' c M _ _).symm,

end

-- theorem baz (n) :
--   (CLCFP.Tinv' V r' c n : CLCFP V r' (rescale N M) c n ⟶ CLCFP V r' M (r' * c * N⁻¹) n) =
--   ((CLCFP.Tinv' V r' (c * N⁻¹) n : CLCFP V r' M (c * N⁻¹) n ⟶ CLCFP V r' M (r' * (c * N⁻¹)) n) ≫
--     (eq_to_hom (by rw mul_assoc) : CLCFP V r' M (r' * (c * N⁻¹)) n ⟶ CLCFP V r' M (r' * c * N⁻¹) n)) :=
-- _.

-- begin
--   suffices :
--     (CLCFP.Tinv' V r' c n : CLCFP V r' (rescale N M) c n ⟶ CLCFP V r' M (r' * c * N⁻¹) n) =
--     ((CLCFP.Tinv V r' (c * N⁻¹) n : CLCFP V r' M (c * N⁻¹) n ⟶ CLCFP V r' M (r' * (c * N⁻¹)) n) ≫
--       (eq_to_hom (by rw mul_assoc) : CLCFP V r' M (r' * (c * N⁻¹)) n ⟶ CLCFP V r' M (r' * c * N⁻¹) n)),


-- end
-- theorem bar (n) :
--   (LCFP.Tinv V r' c n : LCFP V r' (rescale N M) c n ⟶ LCFP V r' M (r' * c * N⁻¹) n) =
--   ((LCFP.Tinv V r' (c * N⁻¹) n : LCFP V r' M (c * N⁻¹) n ⟶ LCFP V r' M (r' * (c * N⁻¹)) n) ≫
--     (eq_to_hom (by rw mul_assoc) : LCFP V r' M (r' * (c * N⁻¹)) n ⟶ LCFP V r' M (r' * c * N⁻¹) n)) :=
-- begin
-- end

example (n) : CLCFPTinv r V r' (rescale N M) c n ≅ CLCFPTinv r V r' M (c * N⁻¹) n :=
begin
  unfold CLCFPTinv,
  dsimp only [foo],
  apply eq_to_iso,
  -- congr,
end

example (n) :
  (BD.complex_X (rescale_constants c' N) r V r' c n).obj M ≅
  BD.complex_X c' r V r' (of r' $ rescale N M) c n :=
begin

end

#print rescale.pseudo_normed_group
#check (by apply_instance : pseudo_normed_group (rescale N M))
#print Tx

end rescale

section double

variables (BD)

open ProFiltPseuNormGrpWithTinv (of)

open category_theory

instance double_suitable : BD.double.suitable c' :=
sorry

-- === !!! warning, the instance for `M × M` has sorry'd data
def double_iso_prod :
  BD.double.complex c' r V r' M c ≅ BD.complex c' r V r' (of r' $ M × M) c :=
sorry

example (N : ℝ≥0) :
  BD.double.complex (rescale_constants c' N) r V r' M c ≅
  BD.complex c' r V r' (of r' $ rescale N (M × M)) c :=
(double_iso_prod BD _ r V _ c) ≪≫ (complex_rescale_iso _ _ _ _ _ _ _)

end double

end breen_deligne
