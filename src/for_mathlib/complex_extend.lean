import algebra.homology.homotopy
import category_theory.abelian.basic

universes v u

noncomputable theory

open category_theory category_theory.limits

variables {ι₁ ι₂ : Type*}

namespace complex_shape

structure embedding (c₁ : complex_shape ι₁) (c₂ : complex_shape ι₂) :=
(f : ι₁ → ι₂)
(r : ι₂ → option ι₁)
(eq_some : ∀ i i', r i = some i' ↔ f i' = i)
(c : ∀ ⦃i j⦄, c₁.rel i j → c₂.rel (f i) (f j))

namespace embedding

def pos_int_to_onat : ℤ → option ℕ
| (n:ℕ)  := n
| -[1+n] := none

def neg_int_to_onat : ℤ → option ℕ
| 0       := (0:ℕ)
| (n+1:ℕ) := none
| -[1+n]  := (n+1:ℕ)

def nat_up_int_up : embedding (complex_shape.up ℕ) (complex_shape.up ℤ) :=
{ f := coe,
  r := pos_int_to_onat,
  eq_some := begin
    rintro (i|i) i',
    { split; { rintro ⟨rfl⟩, refl }, },
    { split; { rintro ⟨⟩, } }
  end,
  c := by { rintro i j (rfl : _ = _), dsimp, refl } }

def nat_down_int_down : embedding (complex_shape.down ℕ) (complex_shape.down ℤ) :=
{ f := coe,
  r := pos_int_to_onat,
  eq_some := begin
    rintro (i|i) i',
    { split; { rintro ⟨rfl⟩, refl }, },
    { split; { rintro ⟨⟩, } }
  end,
  c := by { rintro i j (rfl : _ = _), dsimp, refl } }

def nat_down_int_up : embedding (complex_shape.down ℕ) (complex_shape.up ℤ) :=
{ f := -coe,
  r := neg_int_to_onat,
  eq_some := begin
    rintro ((_|i)|i) (_|i'),
    any_goals { split; { rintro ⟨⟩, } },
    any_goals { split; { rintro ⟨rfl⟩, refl }, },
  end,
  c := by { rintro i j (rfl : _ = _),
    simp only [pi.neg_apply, int.coe_nat_succ, neg_add_rev, up_rel, neg_add_cancel_comm], } }

def nat_up_int_down : embedding (complex_shape.up ℕ) (complex_shape.down ℤ) :=
{ f := -coe,
  r := neg_int_to_onat,
  eq_some := begin
    rintro ((_|i)|i) (_|i'),
    any_goals { split; { rintro ⟨⟩, } },
    any_goals { split; { rintro ⟨rfl⟩, refl }, },
  end,
  c := by { rintro i j (rfl : _ = _),
    simp only [pi.neg_apply, int.coe_nat_succ, neg_add_rev, down_rel, neg_add_cancel_comm] } }

end embedding

end complex_shape

variables {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂}
variables {C : Type*} [category C] [abelian C]

namespace homological_complex

open_locale zero_object

variables (e : c₁.embedding c₂)
variables (X Y Z : homological_complex C c₁) (f : X ⟶ Y) (g : Y ⟶ Z)

def embed.X : option ι₁ → C
| (some i) := X.X i
| none     := 0

def embed.d : Π i j, embed.X X i ⟶ embed.X X j
| (some i) (some j) := X.d i j
| (some i) none     := 0
| none     j        := 0

lemma embed.shape : ∀ (i j : option ι₁)
  (h : ∀ (i' j' : ι₁), i = some i' → j = some j' → ¬ c₁.rel i' j'),
  embed.d X i j = 0
| (some i) (some j) h := X.shape _ _ $ h i j rfl rfl
| (some i) none     h := rfl
| none     j        h := rfl

lemma embed.d_comp_d : ∀ i j k, embed.d X i j ≫ embed.d X j k = 0
| (some i) (some j) (some k) := X.d_comp_d _ _ _
| (some i) (some j) none     := comp_zero
| (some i) none     k        := comp_zero
| none     j        k        := zero_comp

def embed.obj : homological_complex C c₂ :=
{ X := embed.X X ∘ e.r,
  d := λ i j, embed.d X (e.r i) (e.r j),
  shape' := λ i j hij, embed.shape X _ _ begin
    simp only [e.eq_some],
    rintro i' j' rfl rfl h',
    exact hij (e.c h')
  end,
  d_comp_d' := λ i j k hij hjk, embed.d_comp_d X _ _ _ }

variables {X Y Z}

def embed.f : Π i, embed.X X i ⟶ embed.X Y i
| (some i) := f.f i
| none     := 0

lemma embed.comm :  ∀ i j, embed.f f i ≫ embed.d Y i j = embed.d X i j ≫ embed.f f j
| (some i) (some j) := f.comm _ _
| (some i) none     := show _ ≫ 0 = 0 ≫ 0, by simp only [comp_zero]
| none     j        := show 0 ≫ 0 = 0 ≫ _, by simp only [zero_comp]

def embed.map : embed.obj e X ⟶ embed.obj e Y :=
{ f := λ i, embed.f f _,
  comm' := λ i j hij, embed.comm f _ _ }

lemma embed.f_id : ∀ i, embed.f (𝟙 X) i = 𝟙 (embed.X X i)
| (some i) := rfl
| none     := has_zero_object.from_zero_ext _ _

lemma embed.f_comp : ∀ i, embed.f (f ≫ g) i = embed.f f i ≫ embed.f g i
| (some i) := rfl
| none     := has_zero_object.from_zero_ext _ _

def embed : homological_complex C c₁ ⥤ homological_complex C c₂ :=
{ obj := embed.obj e,
  map := λ X Y f, embed.map e f,
  map_id' := λ X, by { ext i, exact embed.f_id _ },
  map_comp' := by { intros, ext i, exact embed.f_comp f g _ } }

end homological_complex
