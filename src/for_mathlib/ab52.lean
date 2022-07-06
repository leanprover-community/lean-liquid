import for_mathlib.ab5

namespace category_theory

universes v u
variables {A : Type u} [category.{v} A] [abelian A]
  [limits.has_colimits A] [AB5 A]

def mono_colim_map_of_mono {J : Type v}
  [small_category J] [is_filtered J] {F G : J ⥤ A}
  (η : F ⟶ G) [∀ i, mono (η.app i)] :
  mono (limits.colim_map η) :=
begin
  haveI : limits.preserves_finite_limits (limits.colim : (J ⥤ A) ⥤ A) :=
    functor.preserves_finite_limits_of_exact _ (AB5.cond A J),
  rw abelian.mono_iff_kernel_ι_eq_zero,
  let e : limits.kernel (limits.colim_map η) ≅ limits.colimit (limits.kernel η) :=
    (limits.preserves_kernel.iso (limits.colim : (J ⥤ A) ⥤ A) η).symm,
  have he : limits.kernel.ι (limits.colim_map η) =
    e.hom ≫ limits.colim_map (limits.kernel.ι η),
  { dsimp [e], rw iso.eq_inv_comp, simp, dsimp [limits.kernel_comparison],
    erw limits.kernel.lift_ι, refl, },
  rw he,
  simp only [preadditive.is_iso.comp_left_eq_zero],
  ext j,
  simp only [limits.ι_colim_map, limits.comp_zero],
  let q : (limits.kernel η).obj j ≅ limits.kernel (η.app j) :=
    limits.preserves_kernel.iso ((evaluation _ A).obj j) η,
  have : (limits.kernel.ι η).app j = q.hom ≫ limits.kernel.ι _,
  { simp, dsimp [limits.kernel_comparison], simp, },
  rw this,
  have : mono (η.app j) := infer_instance,
  rw abelian.mono_iff_kernel_ι_eq_zero at this,
  simp [this],
end

end category_theory
