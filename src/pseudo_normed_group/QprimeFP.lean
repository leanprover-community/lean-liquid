import pseudo_normed_group.FP2
import condensed.adjunctions
import free_pfpng.acyclic
import for_mathlib.derived.ext_coproducts
import for_mathlib.derived.example
import breen_deligne.eval2
import system_of_complexes.shift_sub_id

noncomputable theory

open_locale nnreal

universe u

open category_theory category_theory.limits breen_deligne

section step1

variables (r' : ℝ≥0)
variables (BD : breen_deligne.data) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

abbreviation freeCond := Profinite_to_Condensed.{u} ⋙ CondensedSet_to_Condensed_Ab

def QprimeFP_nat : ℝ≥0 ⥤ chain_complex (Condensed.{u} Ab.{u+1}) ℕ :=
FPsystem r' BD ⟨M⟩ κ ⋙ (freeCond.{u}.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _

def QprimeFP_int : ℝ≥0 ⥤ cochain_complex (Condensed.{u} Ab.{u+1}) ℤ :=
QprimeFP_nat r' BD κ M ⋙ homological_complex.embed complex_shape.embedding.nat_down_int_up

def QprimeFP : ℝ≥0 ⥤ bounded_homotopy_category (Condensed.{u} Ab.{u+1}) :=
QprimeFP_nat r' BD κ M ⋙ chain_complex.to_bounded_homotopy_category

end step1

section step2

variables {r' : ℝ≥0}
variables (BD : breen_deligne.package) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

abbreviation freeCond' := Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_Condensed_Ab

def ProFiltPseuNormGrpWithTinv₁.to_Condensed : Condensed.{u} Ab.{u+1} :=
(PFPNGT₁_to_CHFPNG₁ₑₗ r' ⋙ CHFPNG₁_to_CHFPNGₑₗ.{u} ⋙
  CompHausFiltPseuNormGrp.to_Condensed.{u}).obj M

-- move me
/-- `Tinv : M → M` as hom of condensed abelian groups -/
def _root_.ProFiltPseuNormGrpWithTinv₁.Tinv_cond : M.to_Condensed ⟶ M.to_Condensed :=
(CompHausFiltPseuNormGrp.to_Condensed.{u}).map
  profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv

local attribute [instance] type_pow

set_option pp.universes true

def QprimeFP_incl_aux'' (c : ℝ≥0) (n : ℕ) (M : ProFiltPseuNormGrpWithTinv.{u} r') (i : fin n) :
  (FiltrationPow r' c n).obj M ⟶ ((Filtration r').obj c).obj M :=
((Filtration r').obj c).map $
  profinitely_filtered_pseudo_normed_group_with_Tinv.pi_proj _ _ i

def QprimeFP_incl_aux'
  (c : ℝ≥0) (n : ℕ) (i : (fin n)) (S : Profinite.{u}ᵒᵖ) :
  ulift_functor.{u+1 u}.obj (opposite.unop.{u+2} S ⟶ pseudo_normed_group.filtration_obj.{u} (M ^ n) c) ⟶
  ulift_functor.{u+1 u}.obj ((CompHausFiltPseuNormGrp.of.{u} ↥((PFPNGT₁_to_PFPNG₁ₑₗ.{u} r').obj M)).presheaf (opposite.unop.{u+2} S)) :=
ulift_functor.map $ λ f, ⟨subtype.val ∘ QprimeFP_incl_aux'' c n ⟨M⟩ i ∘ f,
  by refine ⟨_, _, continuous.comp _ _, rfl⟩; apply continuous_map.continuous⟩

instance (n : ℕ) : preserves_limit.{u+1 u+1 u+1 u+1 u+2 u+2}
    (discrete.functor.{u+1 u+1 u+2} (λ (i : ulift.{u+1 0} (fin n)), M.to_Condensed))
    (Condensed_Ab_to_CondensedSet.{u} ⋙ CondensedSet_to_presheaf) :=
sorry -- this should follow directly from the adjunction stuff

universe v

lemma _root_.Ab.ulift_map_apply {A B : Ab.{u}} (f : A ⟶ B) :
  ⇑(Ab.ulift.{v}.map f) = ulift_functor.map f :=
by { ext, refl }

def QprimeFP_incl_aux (c : ℝ≥0) (n : ℕ) :
  (pseudo_normed_group.filtration_obj (M ^ n) c).to_Condensed ⟶
  (Condensed_Ab_to_CondensedSet.obj (⨁ λ (i : ulift (fin n)), M.to_Condensed)) :=
begin
  let x := biproduct.is_limit (λ (i : ulift (fin n)), M.to_Condensed),
  let y := is_limit_of_preserves (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_presheaf) x,
  refine ⟨y.lift ⟨_, ⟨λ i, ⟨_, _⟩, _⟩⟩⟩,
  { refine QprimeFP_incl_aux' _ _ _ i.down, },
  { intros S T f,
    dsimp [QprimeFP_incl_aux', ProFiltPseuNormGrpWithTinv₁.to_Condensed],
    rw [← ulift_functor.map_comp, Ab.ulift_map_apply, ← ulift_functor.map_comp],
    congr' 1, },
  { clear y x,
    rintros ⟨i⟩ ⟨j⟩ ⟨⟨⟨⟩⟩⟩,
    ext S : 2,
    dsimp [QprimeFP_incl_aux', ProFiltPseuNormGrpWithTinv₁.to_Condensed],
    simp only [discrete.functor_map_id, category.id_comp],
    symmetry, apply category.comp_id, }
end
.

set_option pp.universes false

lemma map_FreeAb_comp_map {X Y Z : Type*} [category X] [category Y] [category Z]
  (F : X ⥤ Y) (G : Y ⥤ Z) {α β : FreeAb X} (f : α ⟶ β) :
  (F ⋙ G).map_FreeAb.map f = G.map_FreeAb.map (F.map_FreeAb.map f) :=
begin
  dsimp only [functor.map_FreeAb, functor.comp_map],
  rw [← add_monoid_hom.comp_apply], congr' 1, clear f,
  ext f,
  simp only [free_abelian_group.map_of_apply, functor.comp_map, add_monoid_hom.coe_comp, function.comp_app],
end

def QprimeFP_incl (c : ℝ≥0) :
  (QprimeFP_int r' BD.data κ M).obj c ⟶
  (BD.eval' freeCond').obj M.to_Condensed :=
(homological_complex.embed complex_shape.embedding.nat_down_int_up).map
{ f := λ n, CondensedSet_to_Condensed_Ab.map $ QprimeFP_incl_aux _ _ _,
  comm' := begin
    rintro i j (rfl : _ = _),
    dsimp only [data.eval_functor, functor.comp_obj, functor.flip_obj_obj,
      homological_complex.functor_eval_obj, homological_complex.functor_eval.obj_obj_d,
      data.eval_functor'_obj_d, universal_map.eval_Pow],
    dsimp only [QprimeFP_nat, FPsystem, functor.comp_obj, functor.map_homological_complex_obj_d],
    rw [chain_complex.of_d],
    delta freeCond freeCond',
    rw [functor.comp_map, map_FreeAb_comp_map],
    sorry
  end }

variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

def QprimeFP_sigma_proj :
  ∐ (λ k, (QprimeFP_int r' BD.data κ M).obj (ι k)) ⟶
  (BD.eval' freeCond').obj M.to_Condensed :=
sigma.desc $ λ n, QprimeFP_incl BD κ M _

instance QprimeFP.uniformly_bounded :
  bounded_homotopy_category.uniformly_bounded (λ k, (QprimeFP r' BD.data κ M).obj (ι k)) :=
begin
  use 1, intro k, apply chain_complex.bounded_by_one,
end

end step2

section step3
open bounded_homotopy_category

variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)
variables (A B : ℝ≥0 ⥤ cochain_complex (Condensed.{u} Ab.{u+1}) ℤ)
-- variables [uniformly_bounded (λ k, A.obj (ι k))]

def sigma_shift : ∐ (λ k, A.obj (ι k)) ⟶ ∐ (λ k, A.obj (ι k)) :=
sigma.desc $ λ k, A.map (hom_of_le $ hι $ by { cases k, recover, swap, exact ⟨k.down + 1⟩, apply nat.le_succ }) ≫
  sigma.ι (λ k, A.obj (ι k)) ⟨k.down + 1⟩

def QprimeFP.shift_sub_id : ∐ (λ k, A.obj (ι k)) ⟶ ∐ (λ k, A.obj (ι k)) :=
sigma_shift _ hι _ - 𝟙 _

variables {A B}

def sigma_map (f : A ⟶ B) : ∐ (λ k, A.obj (ι k)) ⟶ ∐ (λ k, B.obj (ι k)) :=
sigma.desc $ λ k, f.app _ ≫ sigma.ι _ k

end step3

section step4

variables {r' : ℝ≥0}
variables (BD : breen_deligne.package) (κ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ c, BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

lemma QprimeFP.short_exact (n : ℤ) :
  short_exact ((QprimeFP.shift_sub_id _ hι _).f n) ((QprimeFP_sigma_proj BD κ M ι).f n) :=
begin
  -- before continuing, we should apply a lemma that says it is sufficient to check this
  -- pointwise on extr.disc.s
  sorry
  -- apply_with short_exact.mk {instances:=ff},
  -- { sorry },
  -- { sorry },
  -- { sorry }
end

end step4

section step5

variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)]
variables (BD : breen_deligne.data)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

def QprimeFP_nat.Tinv [∀ c n, fact (κ c n ≤ r' * κ₂ c n)] :
  (QprimeFP_nat r' BD κ M) ⟶ (QprimeFP_nat r' BD κ₂ M) :=
whisker_right (FPsystem.Tinv.{u} r' BD ⟨M⟩ _ _) _

def QprimeFP_int.Tinv [∀ c n, fact (κ c n ≤ r' * κ₂ c n)] :
  (QprimeFP_int r' BD κ M) ⟶ (QprimeFP_int r' BD κ₂ M) :=
whisker_right (QprimeFP_nat.Tinv _ _ _ _)
  (homological_complex.embed complex_shape.embedding.nat_down_int_up)

def QprimeFP.Tinv [∀ c n, fact (κ c n ≤ r' * κ₂ c n)] :
  (QprimeFP r' BD κ M) ⟶ (QprimeFP r' BD κ₂ M) :=
whisker_right (QprimeFP_nat.Tinv _ _ _ _) chain_complex.to_bounded_homotopy_category

/-- The natural inclusion map -/
def QprimeFP_nat.ι [∀ c n, fact (κ c n ≤ κ₂ c n)] :
  (QprimeFP_nat r' BD κ M) ⟶ (QprimeFP_nat r' BD κ₂ M) :=
whisker_right (FPsystem.res r' BD ⟨M⟩ _ _) _

/-- The natural inclusion map -/
def QprimeFP_int.ι [∀ c n, fact (κ c n ≤ κ₂ c n)] :
  (QprimeFP_int r' BD κ M) ⟶ (QprimeFP_int r' BD κ₂ M) :=
whisker_right (QprimeFP_nat.ι _ _ _ _)
  (homological_complex.embed complex_shape.embedding.nat_down_int_up)

/-- The natural inclusion map -/
def QprimeFP.ι [∀ c n, fact (κ c n ≤ κ₂ c n)] :
  (QprimeFP r' BD κ M) ⟶ (QprimeFP r' BD κ₂ M) :=
whisker_right (QprimeFP_nat.ι _ _ _ _) chain_complex.to_bounded_homotopy_category

open category_theory.preadditive

lemma commsq_shift_sub_id_Tinv [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ r' * κ c n)] :
  commsq (QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD κ₂ M))
  (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.Tinv BD κ₂ κ M))
  (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.Tinv BD κ₂ κ M))
  (QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD κ M)) :=
commsq.of_eq begin
  delta QprimeFP.shift_sub_id,
  rw [sub_comp, comp_sub, category.id_comp, category.comp_id],
  refine congr_arg2 _ _ rfl,
  apply colimit.hom_ext, intro j,
  simp only [sigma_shift, sigma_map, colimit.ι_desc_assoc, colimit.ι_desc,
    cofan.mk_ι_app, category.assoc, nat_trans.naturality_assoc],
end

lemma commsq_shift_sub_id_ι [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ κ c n)] :
  commsq (QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD κ₂ M))
  (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.ι BD κ₂ κ M))
  (sigma_map (λ (k : ulift ℕ), ι k) (QprimeFP_int.ι BD κ₂ κ M))
  (QprimeFP.shift_sub_id ι hι (QprimeFP_int r' BD κ M)) :=
commsq.of_eq begin
  delta QprimeFP.shift_sub_id,
  rw [sub_comp, comp_sub, category.id_comp, category.comp_id],
  refine congr_arg2 _ _ rfl,
  apply colimit.hom_ext, intro j,
  simp only [sigma_shift, sigma_map, colimit.ι_desc_assoc, colimit.ι_desc,
    cofan.mk_ι_app, category.assoc, nat_trans.naturality_assoc],
end

end step5

section step6

variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' ≤ 1)]
variables (BD : breen_deligne.package)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.data.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

open category_theory.preadditive

lemma commsq_sigma_proj_Tinv [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ r' * κ c n)] :
  commsq (QprimeFP_sigma_proj BD κ₂ M ι) (sigma_map (λ (k : ulift ℕ), ι k)
    (QprimeFP_int.Tinv BD.data κ₂ κ M))
  ((BD.eval' freeCond').map M.Tinv_cond)
  (QprimeFP_sigma_proj BD κ M ι) :=
commsq.of_eq begin
  apply colimit.hom_ext, intro j,
  simp only [QprimeFP_sigma_proj, sigma_map, colimit.ι_desc_assoc, colimit.ι_desc,
    cofan.mk_ι_app, category.assoc, nat_trans.naturality_assoc],
  dsimp only [QprimeFP_incl, QprimeFP_int.Tinv, whisker_right_app,
    package.eval', functor.comp_map],
  rw [← functor.map_comp, ← functor.map_comp],
  refine congr_arg _ _,
  ext n : 2,
  dsimp only [homological_complex.comp_f, data.eval_functor, functor.comp_obj, functor.flip_obj_map,
    homological_complex.functor_eval_map_app_f, data.eval_functor'_obj_X_map, functor.comp_map,
    QprimeFP_nat.Tinv, whisker_right_app, functor.map_homological_complex_map_f],
  rw [map_FreeAb_comp_map],
  sorry
end

lemma commsq_sigma_proj_ι [∀ (c : ℝ≥0) (n : ℕ), fact (κ₂ c n ≤ κ c n)] :
  commsq (QprimeFP_sigma_proj BD κ₂ M ι) (sigma_map (λ (k : ulift ℕ), ι k)
    (QprimeFP_int.ι BD.data κ₂ κ M)) (𝟙 _) (QprimeFP_sigma_proj BD κ M ι) :=
commsq.of_eq begin
  simp only [category.comp_id],
  apply colimit.hom_ext, intro j,
  simp only [QprimeFP_sigma_proj, sigma_map, colimit.ι_desc_assoc, colimit.ι_desc,
    cofan.mk_ι_app, category.assoc, nat_trans.naturality_assoc],
  sorry
end

end step6

-- variables (f : ℕ → ℝ≥0)
-- #check ∐ (λ i, (QprimeFP r' BD κ M).obj (f i))
