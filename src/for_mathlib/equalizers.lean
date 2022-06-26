import category_theory.limits.shapes.kernels
import category_theory.preadditive

noncomputable theory

open category_theory

namespace category_theory.limits

variables {C D : Type*} [category C] [category D] (F : C ⥤ D) {X Y : C} (f g : X ⟶ Y)

/-- The fork given by the kernel of the difference of two maps -/
@[simps]
def fork_of_kernel [preadditive C] [has_kernel (f-g)] : fork f g :=
fork.of_ι (kernel.ι (f-g)) (by rw [← sub_eq_zero, ← preadditive.comp_sub, kernel.condition])

/-- In a preadditive category, an equalizer can be constructed as the kernel of the two maps -/
@[simps]
def fork_of_kernel_is_limit [preadditive C] [has_kernel (f-g)] :
  is_limit (fork_of_kernel f g) :=
fork.is_limit.mk _
  (λ s, kernel.lift _ s.ι (by rw [preadditive.comp_sub, sub_eq_zero, fork.condition]))
  (λ s, by apply kernel.lift_ι)
  (λ s m hm, by { ext, simpa only [kernel.lift_ι] using hm, })

/-- The cofork given by the cokernel of the difference of two maps -/
@[simps]
def cofork_of_cokernel [preadditive C] [has_cokernel (f-g)] : cofork f g :=
cofork.of_π (cokernel.π (f-g)) (by rw [← sub_eq_zero, ← preadditive.sub_comp, cokernel.condition])

/-- In a preadditive category, a coequalizer can be constructed as the cokernel of the two maps -/
@[simps]
def cofork_of_cokernel_is_colimit [preadditive C] [has_cokernel (f-g)] :
  is_colimit (cofork_of_cokernel f g) :=
cofork.is_colimit.mk _
  (λ s, cokernel.desc _ s.π (by rw [preadditive.sub_comp, sub_eq_zero, cofork.condition]))
  (λ s, by apply cokernel.π_desc)
  (λ s m hm, by { ext, simpa only [cokernel.π_desc] using hm, })

end category_theory.limits
