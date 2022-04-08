import algebra.homology.homotopy
import category_theory.abelian.basic

universes v u

noncomputable theory

open category_theory category_theory.limits

variables {ι ι' ι₁ ι₂ : Type*}

namespace complex_shape

/-- An embedding `embedding c₁ c₂` between two complex shapes `ι₁` and `ι₂` is
an injection `ι₁ → ι₂` sending related vertices to related vertices. Recall that two
vertices are related in a complex shape iff the differential between them is allowed to
be nonzero. -/
@[nolint has_inhabited_instance]
structure embedding (c₁ : complex_shape ι₁) (c₂ : complex_shape ι₂) :=
(f : ι₁ → ι₂)
(r : ι₂ → option ι₁)
(eq_some : ∀ i₂ i₁, r i₂ = some i₁ ↔ f i₁ = i₂)
(c : ∀ ⦃i j⦄, c₁.rel i j → c₂.rel (f i) (f j))

namespace embedding

lemma r_f {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (i : ι₁) :
  e.r (e.f i) = some i := by rw e.eq_some

lemma r_none {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (i : ι₂)
  (hi: ¬∃ (i₁ : ι₁), i = e.f i₁) : e.r i = none :=
begin
  classical,
  by_contra hi2,
  apply hi,
  obtain ⟨j, hj⟩ := option.ne_none_iff_exists'.1 hi2,
  use j,
  rw e.eq_some at hj,
  rw hj,
end

/-- The map from `ℤ` to `option ℕ` which is `some n` on `n : ℕ : ℤ` and `none otherwise. -/
def pos_int_to_onat : ℤ → option ℕ
| (n:ℕ)  := n
| -[1+n] := none

/-- The map from `ℤ` to `option ℕ` which is `some n` on `-(n : ℕ : ℤ)` and `none otherwise. -/
def neg_int_to_onat : ℤ → option ℕ
| 0       := (0:ℕ)
| (n+1:ℕ) := none
| -[1+n]  := (n+1:ℕ)

/-- The obvious embedding from the ℕ-indexed "cohomological" complex `* → * → * → ...`
  to the corresponding ℤ-indexed complex. -/
def nat_up_int_up : embedding (complex_shape.up ℕ) (complex_shape.up ℤ) :=
{ f := coe,
  r := pos_int_to_onat,
  eq_some := begin
    rintro (i|i) i',
    { split; { rintro ⟨rfl⟩, refl }, },
    { split; { rintro ⟨⟩, } }
  end,
  c := by { rintro i j (rfl : _ = _), dsimp, refl } }

/-- The obvious embedding from the ℕ-indexed "homological" complex `* ← * ← * ← ...`
  to the corresponding ℤ-indexed homological complex. -/
def nat_down_int_down : embedding (complex_shape.down ℕ) (complex_shape.down ℤ) :=
{ f := coe,
  r := pos_int_to_onat,
  eq_some := begin
    rintro (i|i) i',
    { split; { rintro ⟨rfl⟩, refl }, },
    { split; { rintro ⟨⟩, } }
  end,
  c := by { rintro i j (rfl : _ = _), dsimp, refl } }

/-- Obvious embedding from the `ℕ`-indexed homological complex `* ← * ← * ...`
  to `ℤ`-indexed cohomological complex ` ... → * → * → ...` sending $n$ to $-n$
  on the corresponding map `ℕ → ℤ`. -/
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

/-- Obvious embedding from the `ℕ`-indexed cohomological complex `* → * → * ...`
  to `ℤ`-indexed homological complex ` ... ← * ← * ← ...` sending $n$ to $-n$
  on the corresponding map `ℕ → ℤ`. -/
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
variables {cι : complex_shape ι} {cι' : complex_shape ι'}

variables {𝒞 : Type*} [category 𝒞] [abelian 𝒞] -- reclaim category notation!

namespace homological_complex

open_locale zero_object

section embed_X_and_d_basics

/-

`embed`, not to be confused with `embedding` later on, is simply
the extension of constructions involving the index type `ι` of our complex,
to the larger type `option ι`, with `none` being sent to `zero`.

-/
variable (X : homological_complex 𝒞 cι)


/-- If `𝒞` is an abelian category,  and `(Xᵢ)ᵢ` is a `𝒞`-valued homological
complex on a complex-shape with index `ι`, then `embed.X X oi` for `oi : option ι`
is the value `Xᵢ` of `h` at `some i` (an object of `𝒞`), or `0` for `none`. -/
def embed.X : option ι → 𝒞
| (some i) := X.X i
| none     := 0

@[simp] lemma embed.X_none : embed.X X none = 0 := rfl
@[simp] lemma embed.X_some (i : ι) : embed.X X (some i) = X.X i := rfl

/-- The morphism `Xᵢ → Xⱼ` with `i j : option ι` coming from the complex `X`.
Equal to zero if either `i` or `j` is `none`.  -/
def embed.d : Π i j, embed.X X i ⟶ embed.X X j
| (some i) (some j) := X.d i j
| (some i) none     := 0
| none     j        := 0

@[simp] lemma embed.d_some_some (i j : ι) : embed.d X (some i) (some j) = X.d i j :=
rfl

/-- Prop-valued so probably won't break anything. To deal with zerology. -/
instance homological_complex.embed.subsingleton_to_none (c : _) : subsingleton (c ⟶ embed.X X none) :=
@unique.subsingleton _ (has_zero_object.unique_from c)

instance homological_complex.embed.subsingleton_of_none (c) : subsingleton (embed.X X none ⟶ c) :=
@unique.subsingleton _ (has_zero_object.unique_to c)

@[simp] lemma embed.d_to_none (i : option ι) : embed.d X i none = 0 :=
by cases i; refl

@[simp] lemma embed.d_of_none (i : option ι) : embed.d X none i = 0 :=
rfl

lemma embed.shape : ∀ (i j : option ι)
  (h : ∀ (i' j' : ι), i = some i' → j = some j' → ¬ cι.rel i' j'),
  embed.d X i j = 0
| (some i) (some j) h := X.shape _ _ $ h i j rfl rfl
| (some i) none     h := rfl
| none     j        h := rfl

lemma embed.d_comp_d : ∀ i j k, embed.d X i j ≫ embed.d X j k = 0
| (some i) (some j) (some k) := X.d_comp_d _ _ _
| (some i) (some j) none     := comp_zero
| (some i) none     k        := comp_zero
| none     j        k        := zero_comp

end embed_X_and_d_basics

section embedding_change_of_complex

variable (e : cι.embedding cι')

--variables (X Y Z : homological_complex C c₁) (f : X ⟶ Y) (g : Y ⟶ Z)
/-- Object-valued pushforward of `𝒞`-valued homological complexes along an embedding
  `ι₁ ↪ ι₂` of complex-shapes (with all indexes not in the image going to `0`). -/
def embed.obj (X : homological_complex 𝒞 cι) : homological_complex 𝒞 cι' :=
{ X := λ i, embed.X X (e.r i),
  d := λ i j, embed.d X (e.r i) (e.r j),
  shape' := λ i j hij, embed.shape X _ _ begin
    simp only [e.eq_some],
    rintro i' j' rfl rfl h',
    exact hij (e.c h')
  end,
  d_comp_d' := λ i j k hij hjk, embed.d_comp_d X _ _ _ }

variables {X Y Z : homological_complex 𝒞 cι} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Morphism-valued pushforward of `𝒞`-valued homological complexes along an embedding of complex-shapes
( with all morphisms not in the image being defined to be 0) -/
def embed.f : Π i, embed.X X i ⟶ embed.X Y i
| (some i) := f.f i
| none     := 0

-- embed.f f (some j)

@[simp] lemma embed.f_none : embed.f f none = 0 := rfl
@[simp] lemma embed.f_some (i : ι) : embed.f f (some i) = f.f i := rfl

lemma embed.comm :  ∀ i j, embed.f f i ≫ embed.d Y i j = embed.d X i j ≫ embed.f f j
| (some i) (some j) := f.comm _ _
| (some i) none     := show _ ≫ 0 = 0 ≫ 0, by simp only [comp_zero]
| none     j        := show 0 ≫ 0 = 0 ≫ _, by simp only [zero_comp]

/-- Pushforward of a morphism `(Xᵢ)ᵢ ⟶ (Yᵢ)ᵢ` of homological complexes with
  the same complex-shape `ι`, along an embedding of complex shapes c.embedding `ι → ι'` -/
def embed.map : embed.obj e X ⟶ embed.obj e Y :=
{ f := λ i, embed.f f _,
  comm' := λ i j hij, embed.comm f _ _ }

lemma embed.f_id : ∀ i, embed.f (𝟙 X) i = 𝟙 (embed.X X i)
| (some i) := rfl
| none     := has_zero_object.from_zero_ext _ _

lemma embed.f_comp : ∀ i, embed.f (f ≫ g) i = embed.f f i ≫ embed.f g i
| (some i) := rfl
| none     := has_zero_object.from_zero_ext _ _

/-- Functor pushing forward, for a fixed abelian category `𝒞`, the category
of `𝒞`-valued homological complexes of shape `ι₁` along an embedding `ι₁ ↪ ι₂`
(not Lean notation -- fix somehow?) of complexes. -/
def embed : homological_complex 𝒞 cι ⥤ homological_complex 𝒞 cι' :=
{ obj := embed.obj e,
  map := λ X Y f, embed.map e f,
  map_id' := λ X, by { ext i, exact embed.f_id _ },
  map_comp' := by { intros, ext i, exact embed.f_comp f g _ } }
.

def embed_iso (i : ι) : ((embed e).obj X).X (e.f i) ≅ X.X i :=
eq_to_iso
begin
  delta embed embed.obj,
  dsimp,
  rw e.r_f,
  refl,
end

set_option pp.proofs true
lemma foo (i : ι) : (embed_iso e i).hom ≫ f.f i =
  embed.f f (e.r (e.f i)) ≫ (embed_iso e i).hom :=
begin
  rw ← iso.cancel_iso_hom_right _ _ (embed_iso e i).symm,
  simp [embed_iso],
  symmetry,
  rw functor.conj_eq_to_hom_iff_heq,
  have h1 := embed.f_some f i,
  have h2 := e.r_f i,
  rw h2,
  simp,
end


end embedding_change_of_complex

section homotopy

variables {X Y : homological_complex 𝒞 cι}

variables (f f' : X ⟶ Y) (h : homotopy f f')

/-- The morphism `hᵢⱼ: Xᵢ ⟶ Yⱼ` coming from a homotopy between two morphisms of type `X ⟶ Y`.
  Here `X` and `Y` are complexes of shape `ι` and the indices `i j` run over `option ι`. -/
def embed_homotopy_hom : Π (i j : option ι), embed.X X i ⟶ embed.X Y j
| (some i) (some j) := h.hom i j
| (some i) none     := 0
| none     j        := 0

@[simp] lemma embed_homotopy_hom_some (i j : ι) :
  embed_homotopy_hom f f' h (some i) (some j) = h.hom i j := rfl

@[simp] lemma embed_homotopy_hom_eq_zero_of_to_none (oi : option ι) :
  embed_homotopy_hom f f' h oi none = 0 := by cases oi; refl

@[simp] lemma embed_homotopy_hom_eq_zero_of_of_none (oi : option ι) :
  embed_homotopy_hom f f' h none oi = 0 := rfl

lemma embed_homotopy_zero : Π (oi oj : option ι)
  (H : ∀ (i j : ι), oi = some i → oj = some j → ¬ cι.rel j i),
  embed_homotopy_hom f f' h oi oj = 0
| (some i) (some j) H := h.zero i j $ H _ _ rfl rfl
| (some i) none     H := rfl
| none     j        H := rfl

-- lemma embed_homotopy_comm : ∀ (oi oj ok : option ι)
--   (Hij : ∀ (i j : ι), oi = some i → oj = some j → cι.rel i j)
--   (Hjk : ∀ (j k : ι), oj = some j → ok = some k → cι.rel j k),
--   embed.f f oj =
--     embed.d X oj ok ≫ embed_homotopy_hom f f' h ok oj +
--     embed_homotopy_hom f f' h oj oi ≫ embed.d Y oi oj +
--     embed.f f' oj
-- | (some i) (some j) (some k) Hij Hjk := begin
--   have hij : cι.rel i j := Hij _ _ rfl rfl,
--   have hjk : cι.rel j k := Hjk _ _ rfl rfl,
--   have := h.comm j,
--   rw [prev_d_eq _ hij, d_next_eq _ hjk] at this,
--   exact this
-- end
-- | (some i) (some j) none Hij _ := begin
--   have hij : cι.rel i j := Hij _ _ rfl rfl,
--   simp,
--   have h1 := h.comm j,
--   rw [prev_d_eq _ hij] at h1,
--   have h2 := h.comm j,
--   simp at h1,
--   simp at h2,
--   sorry
-- end
-- | none (some _) (some _) _ _ := sorry
-- | none (some _) none _ _ := sorry
-- | none none none _ _ := by { erw [zero_comp, zero_add, zero_add], refl }
-- | none none (some _) _ _ := by { erw [zero_comp, comp_zero, zero_add, zero_add], refl }
-- | (some _) none none _ _ := by { erw [zero_comp, comp_zero, zero_add, zero_add], refl }
-- | (some _) none (some _) _ _ := by { erw [zero_comp, comp_zero, zero_add, zero_add], refl }

-- lemma embed_homotopy_comm' (e : cι.embedding cι') :
--   ∀ (i : option ι) (F : Π i, embed.X X i ⟶ embed.X Y i)
--   (hF : ∀ i, F (e.r i) = let F' := (λ (i j : ι'),
--     show ((embed e).obj X).X i ⟶ ((embed e).obj Y).X j, from
--     embed_homotopy_hom f f' h (e.r i) (e.r j)) in (d_next i) F' + (prev_d i) F'),
--   embed.f f i = F i + embed.f f' i
-- | (some i) F hF := begin
--   convert h.comm i using 2,
--   dsimp at hF, specialize hF (e.f i),
--   sorry
-- end
-- | none     i' H := by ext

-- def loop : complex_shape unit :=
-- { rel := λ _ _, true,
--   next_eq := λ _ _ _ _ _, unit.ext,
--   prev_eq := λ _ _ _ _ _, unit.ext }

-- namespace loop

-- /-- Constructor for the data you need to make a homological complex for the `loop` complex-shape :

-- -/
-- def of_object {A : 𝒞} {d : A ⟶ A} (h : d ≫ d = 0): homological_complex 𝒞 loop :=
-- { X := λ _, A,
--   d := λ _ _, d,
--   shape' := λ _ _ h, (h trivial).elim,
--   d_comp_d' := λ _ _ _ _ _, h }

-- def of_morphism {A B : 𝒞} {dA : A ⟶ A} {dB : B ⟶ B} (hA : dA ≫ dA = 0) (hB : dB ≫ dB = 0)
--   -- morphism from A to B
--   (f : A ⟶ B) (h : f ≫ dB = dA ≫ f)
--   :
-- (of_object hA) ⟶ (of_object hB) :=
-- { f := λ _, f,--begin unfold of, dsimp, end,
--   comm' := λ _ _ _, h }

-- example {A B : 𝒞} {dA : A ⟶ A} {dB : B ⟶ B} (hA : dA ≫ dA = 0) (hB : dB ≫ dB = 0)
-- (f g : A ⟶ B) (hf : f ≫ dB = dA ≫ f) (hg : g ≫ dB = dA ≫ g) -- initial data :
--   -- now what the homotopy means
--   (h : A ⟶ B) :
--   homotopy (of_morphism hA hB f hf) (of_morphism _ _ g hg) :=
-- { hom := λ _ _, h,
--   zero' := λ _ _ h, false.elim $ h trivial,
--   comm := λ ⟨⟩, begin
--     unfold d_next,
--      sorry end }


-- end loop

def embed_homotopy (e : cι.embedding cι') :
  homotopy ((embed e).map f) ((embed e).map f') :=
{ hom := λ i j, embed_homotopy_hom f f' h (e.r i) (e.r j),
  zero' := λ i j hij, embed_homotopy_zero f f' h _ _ begin
    simp only [e.eq_some],
    rintro i' j' rfl rfl h',
    exact hij (e.c h')
  end,
  comm := λ i',  begin
    by_cases hi : ∃ i : ι, i' = e.f i,
    { rcases hi with ⟨i, rfl⟩,
      have this := h.comm i,
      have h4 := e.r_f i,
      -- it's `exact this` modulo `h4`
      delta embed embed.map,
      dsimp only,
      apply_fun (λ x, (embed_iso e i).hom ≫ x ≫ (embed_iso e i).symm.hom) at this,
      convert this,
      { simp only [embed_iso, eq_to_iso.hom, iso.symm_hom, eq_to_iso.inv,
          functor.conj_eq_to_hom_iff_heq],
        rw e.r_f i,
        refl, },
      { simp only [embed_iso, eq_to_iso.hom, iso.symm_hom, eq_to_iso.inv,
  preadditive.add_comp, category.assoc, preadditive.comp_add],
        congr' 2,
        { -- next 30 lines is hacky d_next argument
          rw functor.conj_eq_to_hom_iff_heq,
          delta d_next embed.obj id_rhs embed_homotopy_hom,
          dsimp only,
          induction hi : cι.next i,
          { delta complex_shape.next option.choice at hi,
            split_ifs at hi with h1, cases hi, clear hi,
            simp only [add_monoid_hom.mk'_apply],
            simp only [nonempty_subtype, not_exists] at h1,
            induction hi' : cι'.next (e.f i),
            { simp only,
              rw ← functor.conj_eq_to_hom_iff_heq,
              { simp only [zero_comp, comp_zero] },
              { rw h4, refl },
              { rw h4, refl },
            },
            { cases val with j hj,
              rw h4,
              simp only [heq_iff_eq],
              by_cases hj' : e.r j = none,
              { rw hj', simp only [embed.d_to_none, zero_comp] },
              obtain ⟨i₁, hi₁⟩ := option.ne_none_iff_exists.1 hj',
              rw ← hi₁,
              specialize h1 i₁,
              simp [h.zero' _ _ h1] } },
          { cases val with j hj,
            have cj' : cι'.next (e.f i) = some ⟨e.f j, _⟩ :=
              cι'.next_eq_some (e.c hj),
            rw cj',
            simp only [add_monoid_hom.mk'_apply],
            rw [e.r_f j, h4],
            simp } },
        {
                    rw functor.conj_eq_to_hom_iff_heq,
          delta prev_d embed.obj id_rhs embed_homotopy_hom,
          dsimp only,
          induction hi : cι.prev i,
          { delta complex_shape.prev option.choice at hi,
            split_ifs at hi with h1, cases hi, clear hi,
            simp only [add_monoid_hom.mk'_apply],
            simp only [nonempty_subtype, not_exists] at h1,
            induction hi' : cι'.prev (e.f i),
            { simp only,
              rw ← functor.conj_eq_to_hom_iff_heq,
              { simp only [zero_comp, comp_zero] },
              { rw h4, refl },
              { rw h4, refl },
            },
            { cases val with j hj,
              rw h4,
              simp only [heq_iff_eq],
              by_cases hj' : e.r j = none,
              { rw hj', simp only [embed.d_to_none, zero_comp] },
              obtain ⟨i₁, hi₁⟩ := option.ne_none_iff_exists.1 hj',
              rw ← hi₁,
              specialize h1 i₁,
              simp [h.zero' _ _ h1] } },
          { cases val with j hj,
            rw [cι'.prev_eq_some (e.c hj),add_monoid_hom.mk'_apply],
            simp only [add_monoid_hom.mk'_apply],
            rw [e.r_f j, h4],
            simp },
        },
        { rw [functor.conj_eq_to_hom_iff_heq, e.r_f i],
          refl, } } },
    { -- i' not in image
      have foo := e.r_none _ hi,
      suffices : subsingleton (embed.X X (e.r i') ⟶ embed.X Y (e.r i')),
      { refine @subsingleton.elim _ this _ _ },
      convert (homological_complex.embed.subsingleton_of_none X _),
    },
  end }

end homotopy

end homological_complex

namespace chain_complex

def single₀_comp_embed_iso_single_component (X : 𝒞) : Π (i : ℤ),
  ((single₀ 𝒞 ⋙ homological_complex.embed complex_shape.embedding.nat_down_int_up).obj X).X i ≅
    ((homological_complex.single 𝒞 (complex_shape.up ℤ) 0).obj X).X i
| 0       := iso.refl _
| (n+1:ℕ) := iso.refl _
| -[1+n]  := iso.refl _

def single₀_comp_embed_iso_single :
  single₀ 𝒞 ⋙ homological_complex.embed complex_shape.embedding.nat_down_int_up ≅
    homological_complex.single 𝒞 (complex_shape.up ℤ) 0 :=
nat_iso.of_components
  (λ X, homological_complex.hom.iso_of_components
    (single₀_comp_embed_iso_single_component X)
    (by rintro ((_|i)|i) ((_|j)|j) hij; exact comp_zero.trans zero_comp.symm))
  begin
    intros X Y f,
    ext ((_|i)|i);
    refine (category.comp_id _).trans (eq.trans _ (category.id_comp _).symm);
    dsimp [homological_complex.single],
    { simp only [eq_self_iff_true, category.comp_id, category.id_comp, if_true], refl },
    { rw dif_neg, swap, dec_trivial, refl, },
    { rw dif_neg, swap, dec_trivial, refl, }
  end

end chain_complex
