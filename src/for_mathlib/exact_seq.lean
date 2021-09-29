import algebra.homology.exact
import category_theory.abelian.opposite

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace list

variables {α : Type*} (a : α) (L : list α) (m n : ℕ)

/-- Returns the sublist of `L` starting at index `m` of length `n`
(or shorter, if `L` is too short). -/
def extract := (L.drop m).take n

@[simp] lemma extract_nil : [].extract m n = ([] : list α) :=
by { cases n, refl, cases m, refl, refl }

@[simp] lemma extract_zero_right : L.extract m 0 = [] := rfl

@[simp] lemma extract_cons_succ_left : (a :: L).extract m.succ n = L.extract m n := rfl

end list

example : [0,1,2,3,4,5,6,7,8,9].extract 4 3 = [4,5,6] := rfl

namespace category_theory
variables (𝒞 : Type u) [category.{v} 𝒞]
variables [has_zero_morphisms 𝒞] [has_images 𝒞] [has_kernels 𝒞]
variables {𝒜 : Type u} [category.{v} 𝒜] [abelian 𝒜]

namespace exact -- move this

variables {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C)

instance [exact f g] : exact g.op f.op := sorry

instance {C B A : 𝒜ᵒᵖ} (g : C ⟶ B) (f : B ⟶ A) [exact g f] : exact f.unop g.unop := sorry

end exact

/-- A sequence `[f, g, ...]` of morphisms is exact if the pair `(f,g)` is exact,
and the sequence `[g, ...]` is exact.

Recall that the pair `(f,g)` is exact if `f ≫ g = 0`
and the natural map from the image of `f` to the kernel of `g` is an epimorphism
(equivalently, in abelian categories: isomorphism). -/
inductive exact_seq : list (arrow 𝒞) → Prop
| nil    : exact_seq []
| single : ∀ f, exact_seq [f]
| cons   : ∀ {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (hfg : exact f g) (L) (hgL : exact_seq (g :: L)),
              exact_seq (f :: g :: L)

variable {𝒞}

lemma exact_iff_exact_seq {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) :
  exact f g ↔ exact_seq 𝒞 [f, g] :=
begin
  split,
  { intro h, exact exact_seq.cons f g h _ (exact_seq.single _), },
  { rintro (_ | _ | ⟨A, B, C, f, g, hfg, _, _ | _ | _⟩), exact hfg, }
end

namespace exact_seq

lemma extract : ∀ {L : list (arrow 𝒞)} (h : exact_seq 𝒞 L) (m n : ℕ),
  exact_seq 𝒞 (L.extract m n)
| L (nil)               m     n     := by { rw list.extract_nil, exact nil }
| L (single f)          m     0     := nil
| L (single f)          0     (n+1) := by { cases n; exact single f }
| L (single f)          (m+1) (n+1) := by { cases m; exact nil }
| _ (cons f g hfg L hL) (m+1) n     := extract hL m n
| _ (cons f g hfg L hL) 0     0     := nil
| _ (cons f g hfg L hL) 0     1     := single f
| _ (cons f g hfg L hL) 0     (n+2) := cons f g hfg (L.take n) (extract hL 0 (n+1))

inductive arrow_congr : Π (L L' : list (arrow 𝒞)), Prop
| nil  : arrow_congr [] []
| cons : ∀ {A B : 𝒞} {f f' : A ⟶ B} {L L' : list (arrow 𝒞)} (h : f = f') (H : arrow_congr L L'),
         arrow_congr (f :: L) (f' :: L')

lemma congr : ∀ {L L' : list (arrow 𝒞)}, exact_seq 𝒞 L → arrow_congr L L' → exact_seq 𝒞 L'
| _ _ h arrow_congr.nil                                 := exact_seq.nil
| _ _ h (arrow_congr.cons h₁ arrow_congr.nil)           := exact_seq.single _
| _ _ h (arrow_congr.cons h₁ ((arrow_congr.cons h₂ H))) :=
begin
  substs h₁ h₂,
  rcases h with _ | _ | ⟨A, B, C, f, g, hfg, _, hL⟩,
  refine exact_seq.cons _ _ hfg _ (congr hL (arrow_congr.cons rfl H)),
end

section

lemma of_op : ∀ {L : list (arrow 𝒜)}, exact_seq 𝒜ᵒᵖ (L.reverse.map (λ f, sorry)) →
  exact_seq 𝒜 L := sorry

end

end exact_seq

end category_theory
