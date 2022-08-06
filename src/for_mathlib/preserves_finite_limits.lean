import for_mathlib.split_exact
import category_theory.limits.preserves.shapes.biproducts
import category_theory.limits.constructions.finite_products_of_binary_products

noncomputable theory

universes v u₁ u₂
open_locale tensor_product

open category_theory category_theory.limits opposite

section
variables {𝓐 : Type u₁} {𝓑 : Type u₂} [category.{v} 𝓐] [category.{v} 𝓑] (F : 𝓐 ⥤ 𝓑)
variables [abelian 𝓐] [abelian 𝓑]

def preserves_limits_of_shape_pempty_of_preserves_terminal
  [preserves_limit (functor.empty.{0} 𝓐) F] : preserves_limits_of_shape (discrete pempty) F :=
{ preserves_limit := λ K,
    preserves_limit_of_iso_diagram.{0 0} F (functor.empty_ext (functor.empty 𝓐) _) }

def preserves_terminal_object_of_preserves_zero_morphisms
  [functor.preserves_zero_morphisms F] : preserves_limit (functor.empty.{0} 𝓐) F :=
preserves_terminal_of_iso F $
  (F.map_iso has_zero_object.zero_iso_terminal.symm).trans $
  (functor.map_zero_object F).trans $
  has_zero_object.zero_iso_terminal

def iso_of_ι {X Y : 𝓐} (f g : X ⟶ Y) (c : cone (parallel_pair f g)) :
  c ≅ fork.of_ι (fork.ι c) (fork.condition c) :=
fork.ext (iso.refl _) (by tidy)

def preserves_equalizer_of_preserves_kernels [F.additive]
  [∀ {X Y} (f : X ⟶ Y), preserves_limit (parallel_pair f 0) F] {X Y : 𝓐}
  (f g : X ⟶ Y) : preserves_limit (parallel_pair f g) F :=
begin
  constructor, intros c i,
  let c' := preadditive.is_limit_kernel_fork_of_fork (i.of_iso_limit (iso_of_ι _ _ c)),
  let iFc := is_limit_fork_map_of_is_limit' F (by simp) c',
  apply is_limit.of_iso_limit _ ((cones.functoriality _ F).map_iso (iso_of_ι _ _ c).symm),
  apply (is_limit_map_cone_fork_equiv F (fork.condition c)).inv_fun,
  let p : parallel_pair (F.map (f - g)) 0 ≅ parallel_pair (F.map f - F.map g) 0,
  { exact parallel_pair.ext (iso.refl _) (iso.refl _) (by simp) (by simp) },
  refine is_limit.of_iso_limit (preadditive.is_limit_fork_of_kernel_fork
    ((is_limit.postcompose_hom_equiv p _).symm iFc)) _,
  refine fork.ext (iso.refl _) _,
  dsimp only [p, preadditive.fork_of_kernel_fork, cones.postcompose, ← fork.app_zero_eq_ι],
  simp [- fork.app_zero_eq_ι]
end

def preserves_equalizers_of_preserves_kernels [F.additive]
  [∀ {X Y} (f : X ⟶ Y), preserves_limit (parallel_pair f 0) F] :
  preserves_limits_of_shape walking_parallel_pair F :=
{ preserves_limit := λ K,
  begin
    letI := preserves_equalizer_of_preserves_kernels F
      (K.map walking_parallel_pair_hom.left) (K.map walking_parallel_pair_hom.right),
    apply preserves_limit_of_iso_diagram F (diagram_iso_parallel_pair K).symm
  end }

-- todo: unify with `exact_comp_mono_iff`
lemma exact_comp_mono_iff' {X Y Z A : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ A) [mono h]:
  exact f (g ≫ h) ↔ exact f g :=
begin
  refine ⟨λ hfg, ⟨zero_of_comp_mono h (by rw [category.assoc, hfg.1]), _⟩, λ h, exact_comp_mono h⟩,
  rw ← (iso.eq_comp_inv _).1 (image_to_kernel_comp_mono _ _ h hfg.1),
  haveI := hfg.2, apply epi_comp
end

end

set_option pp.universes true
lemma preserves_finite_limits_of_preserves_mono_preserves_finite_colimits
  {𝓐 : Type u₁} {𝓑 : Type u₂} [category.{v} 𝓐] [category.{v} 𝓑] [abelian 𝓐] [abelian 𝓑]
  (F : 𝓐 ⥤ 𝓑) (h1 : ∀ ⦃X Y : 𝓐⦄ (f : X ⟶ Y), mono f → mono (F.map f))
  [preserves_finite_colimits F] :
  preserves_finite_limits F :=
begin
  haveI : preserves_binary_biproducts F,
  { apply preserves_binary_biproducts_of_preserves_binary_coproducts },
  haveI : preserves_limits_of_shape (discrete walking_pair) F,
  { apply preserves_binary_products_of_preserves_binary_biproducts },
  haveI : F.additive,
  { apply functor.additive_of_preserves_binary_biproducts },
  haveI : ∀ {X Y} (f : X ⟶ Y), preserves_limit (parallel_pair f 0) F,
  { intros X Y f,
    constructor,
    intros c hc,
    suffices hF : exact (F.map (fork.ι c)) (F.map f),
    { haveI : mono (F.map (fork.ι c)),
      { apply h1,
        exact limits.mono_of_is_limit_fork hc },
      let := abelian.is_limit_of_exact_of_mono _ _ hF,
      let α : parallel_pair f 0 ⋙ F ≅ parallel_pair (F.map f) 0,
      { refine diagram_iso_parallel_pair _ ≪≫ _,
        refine parallel_pair.ext (iso.refl _) (iso.refl _) (by simp) (by simp) },
      refine is_limit.postcompose_hom_equiv α _ _,
      refine this.of_iso_limit (cones.ext (iso.refl _) _),
      rintro (_|_),
      { simp, dsimp, simp },
      { simp } },
    let hc' := hc.of_iso_limit (iso_of_ι _ _ _),
    have := abelian.exact_of_is_kernel _ _ (kernel_fork.condition c) hc',
    simp_rw ← image.fac f at this,
    rw exact_comp_mono_iff' at this,
    let := abelian.is_colimit_of_exact_of_epi _ _ this,
    let q := is_colimit_cofork_map_of_is_colimit' F _ this,
    haveI : mono (F.map (image.ι f)),
    { apply h1, apply_instance },
    simp_rw ← image.fac f,
    rw [functor.map_comp, exact_comp_mono_iff'],
    exact abelian.exact_of_is_cokernel _ _ _ q },
  haveI : preserves_limits_of_shape walking_parallel_pair F,
  { apply preserves_equalizers_of_preserves_kernels },
  haveI : preserves_limit (functor.empty.{0} 𝓐) F,
  { apply preserves_terminal_object_of_preserves_zero_morphisms },
  haveI : preserves_limits_of_shape (discrete.{0} pempty) F,
  { apply limits.preserves_limits_of_shape_pempty_of_preserves_terminal, },
  haveI p := preserves_finite_products_of_preserves_binary_and_terminal F,
  exact @preserves_finite_limits_of_preserves_equalizers_and_finite_products
    _ _ _ _ _ _ _ _ p,
end
