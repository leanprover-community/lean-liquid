import algebra.group.pi
import data.nat.cast

-- move this
lemma pi.nat_apply {α β : Type*} [has_zero β] [has_one β] [has_add β] :
  ∀ (n : ℕ) (a : α), (n : α → β) a = n
| 0     a := rfl
| (n+1) a := show (n : α → β) a + (1 : α → β) a = n + 1, by { rw pi.nat_apply, refl }
.

-- move this
@[simp] lemma pi.coe_nat {α β : Type*} [has_zero β] [has_one β] [has_add β] (n : ℕ) :
  (n : α → β) = λ _, n :=
by { ext, rw pi.nat_apply }
