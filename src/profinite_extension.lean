import topology.category.Profinite
import topology.bounded_continuous_function

open_locale bounded_continuous_function

section immersion

variables (X Y : Type*) [topological_space X] [topological_space Y]

/-- Closed immersion of a topological space `X` into a topological space `Y`. -/
structure closed_immersion :=
(to_fun : X → Y)
(hincl₁ : function.injective to_fun)
(hincl₂ : continuous to_fun)
(hincl₃ : is_closed_map to_fun)

instance : has_coe_to_fun (closed_immersion X Y) :=
{ F := λ _, X → Y,
  coe := λ f, f.to_fun }

end immersion

section profinite

variables {W : Type*} [normed_group W] [complete_space W]
variables {A B : Profinite} (incl : closed_immersion A B)
variables {ε : ℝ} (hε : 0 < ε)

include hε incl

/-- Given a complete normed group `W`, profinite set `A`, and bounded continuous function
`f : A → W`, and a closed immersion of `A` into another profinite set `B`, there exists a
continuous function from `B` to `W` ... -/
def extend_aux (f : A →ᵇ W) : C(B, W) :=
sorry

variables {incl hε}

/-- ... which is also bounded, with norm a factor of most `1 + ε` greater .... -/
lemma norm_extend_aux (f : A →ᵇ W) (x : B) : ∥extend_aux incl hε f x∥ ≤ (1 + ε) * ∥f∥ :=
sorry

variables (incl hε)

/-- (digression: let's bundle it as a bounded continuous function) -/
noncomputable def extend (f : A →ᵇ W) : B →ᵇ W :=
bounded_continuous_function.of_normed_group (extend_aux incl hε f)
  (extend_aux incl hε f).continuous _ (norm_extend_aux f)

variables {incl hε}

/-- (digression:  here's the norm for the bundled map) -/
lemma norm_extend (f : A →ᵇ W) : ∥extend incl hε f∥ ≤ (1 + ε) * ∥f∥ :=
bounded_continuous_function.norm_of_normed_group_le _ (by nlinarith [norm_nonneg f]) _

/-- ... and which is an extension of `f`. -/
lemma is_extend (f : A →ᵇ W) :
  (extend incl hε f) ∘ incl = f :=
sorry

end profinite
