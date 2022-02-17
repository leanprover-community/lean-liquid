import condensed.projective_resolution

namespace condensed

open category_theory.limits
--TODO: generalize (as needed...)
universe u
variables {A B : Condensed.{u} Ab.{u+1}} (f : A ⟶ B)

def kernel_iso (S : ExtrDisc.{u}) :
  (Condensed.evaluation _ S.val).obj (kernel f) ≅
  kernel ((Condensed.evaluation _ S.val).map f) := sorry

@[simp, reassoc]
lemma kernel_iso_hom (S : ExtrDisc.{u}) :
  (kernel_iso f S).hom ≫ kernel.ι _ = (Condensed.evaluation _ S.val).map (kernel.ι _) :=
sorry

def cokernel_iso (S : ExtrDisc.{u}) :
  cokernel ((Condensed.evaluation _ S.val).map f) ≅
  (Condensed.evaluation _ S.val).obj (cokernel f) := sorry

@[simp, reassoc]
lemma cokernel_iso_hom (S : ExtrDisc.{u}) :
  cokernel.π _ ≫ (cokernel_iso f S).hom = (Condensed.evaluation _ S.val).map (cokernel.π _) :=
sorry

end condensed
