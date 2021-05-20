import thm95.constants
import thm95.double_complex
import prop_92.prop_92
import normed_snake_dual

noncomputable theory

open_locale nnreal big_operators nat
open category_theory opposite simplex_category

universe variables u v w u₀

namespace thm95

variables (BD : breen_deligne.data) (c_ : ℕ → ℝ≥0) [BD.suitable c_]
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : SemiNormedGroup.{v})
variables (Λ : PolyhedralLattice.{u}) (M : ProFiltPseuNormGrpWithTinv.{w} r')
variables (N : ℕ) [fact (0 < N)] (n : ℕ)

section
open PolyhedralLattice

def CLCFP' : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ ℝ≥0ᵒᵖ ⥤ SemiNormedGroup :=
(ProFiltPseuNormGrpWithTinv.Pow r' n ⋙ (Filtration r').flip).op ⋙
  functor.op_hom _ _ ⋙ (whiskering_right ℝ≥0ᵒᵖ Profiniteᵒᵖ _).obj (CLC V)

def cosimplicial_SemiNormedGroup : simplex_category ⥤ (ℝ≥0ᵒᵖ ⥤ SemiNormedGroup) :=
Cech_nerve r' Λ M N ⋙ CLCFP' r' V n

def col_augmentation_map :
  (CLCFP' r' V n).obj ((PolyhedralLattice.Hom M).obj Λ) ⟶
    (cosimplicial_SemiNormedGroup r' V Λ M N n).obj (mk 0) :=
(CLCFP' r' V n).map (Cech_augmentation_map r' Λ M N)

def col_complex_aux : cochain_complex (ℝ≥0ᵒᵖ ⥤ SemiNormedGroup) ℕ :=
alt_face_map_cocomplex (col_augmentation_map r' V Λ M N n)
begin
  dsimp only [col_augmentation_map, cosimplicial_SemiNormedGroup,
    category_theory.functor.comp_map, Cech_augmentation_map, Cech_nerve,
    cosimplicial_augmentation_map, cosimplicial],
  simp only [← functor.map_comp],
  rw augmentation_map_equalizes (diagonal_embedding Λ N),
end

def col_complex : system_of_complexes :=
(col_complex_aux r' V Λ M N n).as_functor

def col_complex_rescaled_aux : cochain_complex (ℝ≥0ᵒᵖ ⥤ SemiNormedGroup) ℕ :=
(col_complex_aux r' V Λ M N n).modify
  thm95.rescale_functor'
  thm95.rescale_nat_trans'

def col_complex_rescaled : system_of_complexes :=
(col_complex_rescaled_aux r' V Λ M N n).as_functor

end

namespace col_complex_rescaled

open polyhedral_lattice (Hom)
open PolyhedralLattice (cosimplicial)

lemma X_zero' (c : ℝ≥0ᵒᵖ) :
  ((col_complex_rescaled r' V Λ M N n).obj c).X 0 =
    (CLCFP V r' c.unop n).obj (op $ Hom Λ M) := rfl

lemma X_zero (c : ℝ≥0) :
  (col_complex_rescaled r' V Λ M N n) c 0 = (CLCFP V r' c n).obj (op $ Hom Λ M) := rfl

lemma X_one (c : ℝ≥0) :
  (col_complex_rescaled r' V Λ M N n) c 1 =
    (CLCFP V r' c n).obj ((op $ Hom ((cosimplicial Λ N).obj (mk 0)) M)) := rfl

instance move_pls (r' : ℝ≥0) (c : ℝ≥0ᵒᵖ) : fact (unop (r'.MulLeft.op.obj c) ≤ r' * unop c) :=
⟨le_rfl⟩

instance move_pls2 (c : ℝ≥0ᵒᵖ) : fact (unop (r'.MulLeft.op.obj c) ≤ unop c) :=
by { dsimp [nnreal.MulLeft], apply_instance }

def T_inv_sub_Tinv_f_succ_succ [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  ((col_complex_rescaled.{u v w u₀} r' V Λ M N n).obj c).X (i + 2) ⟶
    (((col_complex_rescaled.{u v w u₀} r' V Λ M N n).scale_index_left r').obj c).X (i + 2) :=
(SemiNormedGroup.rescale (i+2)!).map $ (CLCFP.T_inv_sub_Tinv r r' V _ _ n).app _

def T_inv_sub_Tinv_f [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  Π i, ((col_complex_rescaled.{u v w u₀} r' V Λ M N n).obj c).X i ⟶
  (((col_complex_rescaled.{u v w u₀} r' V Λ M N n).scale_index_left r').obj c).X i
| 0     := (CLCFP.T_inv_sub_Tinv r r' V _ _ n).app _
| 1     := (CLCFP.T_inv_sub_Tinv r r' V _ _ n).app _
| (i+2) := T_inv_sub_Tinv_f_succ_succ r r' V Λ M N n c i

lemma T_inv_sub_Tinv_comm [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  ∀ i, T_inv_sub_Tinv_f r r' V Λ M N n c i ≫ (((col_complex_rescaled r' V Λ M N n).scale_index_left r').obj c).d i (i+1) =
    ((col_complex_rescaled r' V Λ M N n).obj c).d i (i+1) ≫ T_inv_sub_Tinv_f r r' V Λ M N n c (i+1)
| 0     := sorry -- by { ext, dsimp [T_inv_sub_Tinv_f, system_of_complexes.scale_index_left, nnreal.MulLeft], sorry }
| 1     := sorry
| (i+2) := sorry

def T_inv_sub_Tinv [normed_with_aut r V] :
  col_complex_rescaled r' V Λ M N n ⟶ (col_complex_rescaled r' V Λ M N n).scale_index_left r' :=
{ app := λ c,
  { f := T_inv_sub_Tinv_f r r' V Λ M N n c,
    comm' := sorry },
  naturality' := sorry }

end col_complex_rescaled

namespace double_complex

open polyhedral_lattice (Hom)

local attribute [semireducible] CLCFPTinv CLCFPTinv₂ CLCFP -- CLCTinv

lemma col_obj_X_zero [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  (((double_complex BD c_ r r' V Λ M N).col n).obj c).X 0 =
  (CLCFPTinv r V r' (c.unop * c_ n) (BD.X n)).obj (op $ Hom Λ M) := rfl

-- local attribute [semireducible] opposite

def col_ι_f_succ_succ [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  (((double_complex.{u v w u₀} BD c_ r r' V Λ M N).col n).obj c).X (i+2) ⟶
    (((col_complex_rescaled.{u v w u₀} r' V Λ M N (BD.X n)).scale_index_right (c_ n)).obj c).X (i+2) :=
(SemiNormedGroup.rescale (i+2)!).map (CLCTinv.ι r V _ _)

def col_ι_f [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  Π i, (((double_complex.{u v w u₀} BD c_ r r' V Λ M N).col n).obj c).X i ⟶
       (((col_complex_rescaled.{u v w u₀} r' V Λ M N (BD.X n)).scale_index_right (c_ n)).obj c).X i
| 0     := CLCTinv.ι r V _ _
| 1     := CLCTinv.ι r V _ _
| (i+2) := col_ι_f_succ_succ _ _ _ _ _ _ _ _ _ _ i

lemma col_ι [normed_with_aut r V] :
  (double_complex.{u v w u₀} BD c_ r r' V Λ M N).col n ⟶
    (col_complex_rescaled.{u v w u₀} r' V Λ M N (BD.X n)).scale_index_right (c_ n) :=
{ app := λ c,
  { f := col_ι_f BD c_ r r' V Λ M N n c,
    comm' := sorry },
  naturality' := sorry }

end double_complex

namespace col_complex_rescaled

lemma admissible : (col_complex_rescaled r' V Λ M N n).admissible := sorry

lemma is_weak_bounded_exact (m : ℕ) (tom jerry micky : ℝ≥0) [fact (1 ≤ tom)] :
  (col_complex_rescaled r' V Λ M N n).is_weak_bounded_exact tom jerry m micky :=
sorry

end col_complex_rescaled

open universal_constants (hiding N)

set_option pp.universes true

lemma col_exact' [normed_with_aut r V] [fact (r < 1)] (m : ℕ)
  (tom jerry micky : ℝ≥0) [fact (1 ≤ tom)] (huey dewey louie : ℝ≥0) [fact (1 ≤ huey)]
   (ε : ℝ≥0) (hε : 0 < ε) :
  ((double_complex.{u v w u₀} BD c_ r r' V Λ M N).col n).is_weak_bounded_exact (k₁ m) (K₁ m) m (c₀ m Λ) :=
begin
  have adm := (col_complex_rescaled.admissible.{u v w u₀} r' V Λ M N (BD.X n)),
  have adm2 := adm.scale_index_left r',
  let T_T := (system_of_complexes.ScaleIndexRight (c_ n)).map
    (col_complex_rescaled.T_inv_sub_Tinv r r' V Λ M N (BD.X n)),
  have key := weak_normed_snake_dual
    ((double_complex.{u v w u₀} BD c_ r r' V Λ M N).col n) _ _
    (double_complex.col_ι BD c_ r r' V Λ M N n) T_T
    _ _ _ _ (1 + r⁻¹) (r / (1 - r) + ε)
    ((col_complex_rescaled.is_weak_bounded_exact.{u v w u₀}
      r' V Λ M N _ (m + 1) tom jerry micky).scale_index_right _ adm)
    (((col_complex_rescaled.is_weak_bounded_exact.{u v w u₀}
      r' V Λ M N _ (m + 1) huey dewey louie).scale_index_left _ adm).scale_index_right _ adm2)
    (adm.scale_index_right _),
  have hk : k₁ m = tom * huey, { sorry },
  have hK : K₁ m = (jerry + (1 + r⁻¹) * (r / (1 - r) + ε) * jerry * dewey), { sorry },
  simp only [hk, hK],
  convert key _ _ _ _, swap 8, { exact ⟨le_rfl⟩ },
  any_goals { clear key },
  { intros c i x,
    -- probably split this off into a different lemma
    -- for `i = 0,1` we don't need to do anything
    -- for `i >= 2` we need to use `SemiNormedGroup.rescale`
    -- in both cases, we then use
    have := CLCFP.T_inv_sub_Tinv_bound_by r r' V,
    sorry },
  { intros c hc i hi y,
    -- probably split this off into a different lemma
    -- for `i = 0,1` we don't need to do anything
    -- for `i >= 2` we need to use `SemiNormedGroup.rescale`
    -- in both cases, we then use
    have := @CLCFP.T_inv_sub_Tinv_exists_preimage r r' V,
    sorry },
  -- split off the next 4 sorrys
  { sorry },
  { sorry },
  { sorry },
  { sorry },
end

end thm95
