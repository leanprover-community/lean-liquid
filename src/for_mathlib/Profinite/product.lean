import category_theory.limits.shapes.binary_products
import topology.category.Profinite

namespace Profinite

universe u
variables (X Y : Profinite.{u})

open category_theory.limits
open category_theory

/-- An explicit cone for the product of two profinite sets. -/
@[simps]
def prod_cone : cone (pair X Y) :=
{ X := Profinite.of (X × Y),
  π :=
  { app := λ i,
  match i with
  | walking_pair.left := ⟨prod.fst⟩
  | walking_pair.right := ⟨prod.snd⟩
  end } } .

/-- The explicit cone for the product of two profinite sets is a limit cone. -/
@[simps]
def is_limit_prod_cone : is_limit (prod_cone X Y) :=
{ lift := λ S,
  { to_fun := λ t, ⟨S.π.app walking_pair.left t, S.π.app walking_pair.right t⟩ },
  fac' := begin
    rintros S (_|_),
    { ext, refl },
    { ext, refl }
  end,
  uniq' := begin
    rintros S m h,
    ext,
    { specialize h walking_pair.left,
      apply_fun (λ e, e x) at h,
      exact h },
    { specialize h walking_pair.right,
      apply_fun (λ e, e x) at h,
      exact h },
  end }

@[simps hom inv]
noncomputable def prod_iso : X ⨯ Y ≅ Profinite.of (X × Y) :=
(limit.is_limit _).cone_point_unique_up_to_iso (is_limit_prod_cone X Y)

end Profinite
