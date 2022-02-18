import condensed.projective_resolution

namespace condensed

open category_theory.limits
open category_theory
--TODO: generalize (as needed...)
universe u
variables {A B : Condensed.{u} Ab.{u+1}} (f : A ⟶ B)

noncomputable theory

def kernel_diagram_iso {A B : Condensed.{u} Ab.{u+1}} (S : ExtrDisc) (f : A ⟶ B) :
  parallel_pair f 0 ⋙ Condensed.evaluation Ab S.val ≅
    parallel_pair ((Condensed.evaluation Ab S.val).map f) 0 :=
nat_iso.of_components (λ X,
  match X with
  | walking_parallel_pair.zero := iso.refl _
  | walking_parallel_pair.one := iso.refl _
  end) $ by { rintros (a|a) (b|b) (f|f), tidy }

def cokernel_diagram_iso {A B : Condensed.{u} Ab.{u+1}} (S : ExtrDisc) (f : A ⟶ B) :
  limits.parallel_pair ((Condensed.evaluation Ab S.val).map f) 0 ≅
    limits.parallel_pair f 0 ⋙ Condensed.evaluation Ab S.val :=
nat_iso.of_components (λ X,
  match X with
  | walking_parallel_pair.zero := iso.refl _
  | walking_parallel_pair.one := iso.refl _
  end) $ by { rintros (a|a) (b|b) (f|f), tidy }

def kernel_iso (S : ExtrDisc.{u}) :
  (Condensed.evaluation _ S.val).obj (kernel f) ≅
  kernel ((Condensed.evaluation _ S.val).map f) :=
(is_limit_of_preserves (Condensed.evaluation _ S.val)
  (limit.is_limit (parallel_pair f 0))).cone_point_unique_up_to_iso
  (limit.is_limit _) ≪≫ has_limit.iso_of_nat_iso (kernel_diagram_iso _ _)

@[simp, reassoc]
lemma kernel_iso_hom (S : ExtrDisc.{u}) :
  (kernel_iso f S).hom ≫ kernel.ι _ = (Condensed.evaluation _ S.val).map (kernel.ι _) :=
begin
  dsimp [kernel_iso, kernel_diagram_iso],
  simp only [category.assoc, has_limit.iso_of_nat_iso_hom_π,
    nat_iso.of_components.hom_app, limit.cone_point_unique_up_to_iso_hom_comp_assoc,
    functor.map_cone_π_app, equalizer.fork_π_app_zero,
    equalizer_as_kernel, Condensed.evaluation_map],
  apply category.comp_id,
end

def cokernel_iso (S : ExtrDisc.{u}) :
  cokernel ((Condensed.evaluation _ S.val).map f) ≅
  (Condensed.evaluation _ S.val).obj (cokernel f) :=
has_colimit.iso_of_nat_iso (cokernel_diagram_iso _ _) ≪≫
  (colimit.is_colimit _).cocone_point_unique_up_to_iso
  (is_colimit_of_preserves (Condensed.evaluation _ _)
  (colimit.is_colimit (parallel_pair f 0)))

@[simp, reassoc]
lemma cokernel_iso_hom (S : ExtrDisc.{u}) :
  cokernel.π _ ≫ (cokernel_iso f S).hom = (Condensed.evaluation _ S.val).map (cokernel.π _) :=
begin
  dsimp [cokernel_iso, cokernel_diagram_iso],
  simp only [has_colimit.iso_of_nat_iso_ι_hom_assoc, nat_iso.of_components.hom_app,
  colimit.comp_cocone_point_unique_up_to_iso_hom, functor.map_cocone_ι_app,
  coequalizer.cofork_ι_app_one, coequalizer_as_cokernel, Condensed.evaluation_map],
  apply category.id_comp,
end

end condensed
