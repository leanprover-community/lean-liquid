import order.filter.at_top_bot
import for_mathlib.order_basic

open filter
open_locale filter

variables {X : Type*}

lemma filter.tendsto.subseq_mem {F : filter X} {V : ℕ → set X} (hV : ∀ n, V n ∈ F) {u : ℕ → X} (hu : tendsto u at_top F) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, u (φ n) ∈ V n :=
strict_mono_forall_of_eventually' (λ n, tendsto_at_top'.mp hu _ (hV n) : ∀ n, ∃ N, ∀ k ≥ N, u k ∈ V n)

lemma tendsto_at_top_diagonal {α : Type*} [semilattice_sup α] : tendsto (λ a : α, (a, a)) at_top at_top :=
by { rw ← prod_at_top_at_top_eq, exact tendsto_id.prod_mk tendsto_id }

lemma filter.tendsto.prod_map_prod_at_top {α β γ : Type*} [semilattice_sup γ] {F : filter α} {G : filter β}
  {f : α → γ} {g : β → γ} (hf : tendsto f F at_top) (hg : tendsto g G at_top) :
  tendsto (prod.map f g) (F ×ᶠ G)  at_top :=
by { rw ← prod_at_top_at_top_eq, exact hf.prod_map hg, }

lemma filter.tendsto.prod_at_top {α γ : Type*} [semilattice_sup α] [semilattice_sup γ]
  {f g : α → γ} (hf : tendsto f at_top at_top) (hg : tendsto g at_top at_top) :
  tendsto (prod.map f g) at_top  at_top :=
by { rw ← prod_at_top_at_top_eq, exact hf.prod_map_prod_at_top hg, }

lemma filter.eventually_at_top_prod_self {α : Type*} [semilattice_sup α] [nonempty α] {p : α × α → Prop} :
  (∀ᶠ x in at_top, p x) ↔ (∃ a, ∀ k l, k ≥ a → l ≥ a → p (k, l)) :=
by simp [← prod_at_top_at_top_eq, at_top_basis.prod_self.eventually_iff]

lemma filter.eventually_at_top_prod_self' {α : Type*} [semilattice_sup α] [nonempty α] {p : α × α → Prop} :
  (∀ᶠ x in at_top, p x) ↔ (∃ a, ∀ k ≥ a, ∀ l ≥ a, p (k, l)) :=
begin
  rw filter.eventually_at_top_prod_self,
  apply exists_congr,
  tauto,
end
