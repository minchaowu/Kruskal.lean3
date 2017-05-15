import .finset.to_set .finite


namespace set

variable {A : Type}

noncomputable definition card (s : set A) := finset.card (set.to_finset s)

theorem card_to_set (s : finset A) : card (finset.to_set s) = finset.card s :=
by rewrite [↑card, to_finset_to_set]

end set
