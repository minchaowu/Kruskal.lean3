import .finset.to_set .finite data.set
open nat classical

namespace set

variable {A : Type}

noncomputable definition card (s : set A) := finset.card (set.to_finset s)

theorem card_to_set (s : finset A) : card (finset.to_set s) = finset.card s :=
by simp [card, (to_finset_to_set s)] 

theorem card_of_not_finite {s : set A} (nfins : ¬ finite s) : card s = 0 :=
by simp [card, (to_finset_of_not_finite nfins)]; apply finset.card_empty

theorem card_empty : card (∅ : set A) = 0 :=
by rw [-finset.to_set_empty, card_to_set]; apply finset.card_empty

theorem card_insert_of_mem {a : A} {s : set A} (H : a ∈ s) : card (insert a s) = card s :=
if fins : finite s then
by simp [card]; rw to_finset_insert; rw -mem_to_finset_eq at H; rw [finset.card_insert_of_mem H]
else
  (have ¬ finite (insert a s), from suppose _, absurd (finite_of_finite_insert this) fins,
by rw [card_of_not_finite fins, card_of_not_finite this])

theorem card_insert_of_not_mem {a : A} {s : set A} [finite s] (H : ¬ a ∈ s) :
  card (insert a s) = card s + 1 :=
begin 
simp [card]; rw [to_finset_insert, finset.card_insert_of_not_mem], simp, 
rw -mem_to_finset_eq at H, exact H
end

theorem card_insert_le (a : A) (s : set A) [finite s] :
  card (insert a s) ≤ card s + 1 :=
if H : a ∈ s then by rewrite [card_insert_of_mem H]; apply le_succ
else by rewrite [card_insert_of_not_mem H]

theorem card_singleton (a : A) : card (insert a (∅:set A)) = 1 :=
have ¬ a ∈ ∅, from not_mem_empty _,
begin rw [card_insert_of_not_mem this, card_empty] end

-- Note : have to provide the predicate explicitly.

theorem eq_empty_of_card_eq_zero {s : set A} [finite s] : card s = 0 → s = ∅ :=
@induction_on_finite _ (λ x, card x = 0 → x = ∅) s _
  (by intro H; exact rfl)
  (begin
    intros a s' fins' anins IH H,
    rewrite (card_insert_of_not_mem anins) at H,
    contradiction
  end)


theorem card_upto (n : ℕ) : card {i | i < n} = n :=
by simp [card]; rw [to_finset_upto, finset.card_upto]

-- theorem card_add_card (s₁ s₂ : set A) [finite s₁] [finite s₂] :
--   card s₁ + card s₂ = card (s₁ ∪ s₂) + card (s₁ ∩ s₂) :=
-- begin
--   rw [-to_set_to_finset s₁, -to_set_to_finset s₂],
--   rw [-finset.to_set_union, -finset.to_set_inter], 
--   repeat {rw card_to_set},
--   -- apply finset.card_add_card
-- end

end set
