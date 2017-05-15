import .finset.to_set

open nat classical

variable {A : Type}

noncomputable instance type_decidable_eq (A : Type) : decidable_eq A :=
λ a b, prop_decidable (a = b)

namespace set

attribute [class]
definition finite (s : set A) : Prop := ∃ (s' : finset A), s = ↑s'

attribute [instance]
theorem finite_finset (s : finset A) : finite (finset.to_set s) :=
exists.intro s rfl

noncomputable instance dec_finite (s : set A) : decidable (finite s) := prop_decidable (finite s)

noncomputable definition to_finset (s : set A) : finset A :=
if fins : finite s then some fins else finset.empty

theorem to_finset_of_not_finite {s : set A} (nfins : ¬ finite s) : to_finset s = finset.empty := 
dif_neg nfins

theorem to_set_to_finset (s : set A) [fins : finite s] : ↑(to_finset s) = s :=
have to_finset s = some fins, from dif_pos fins,
by rw this; exact eq.symm (some_spec fins)

-- theorem mem_to_finset_eq (a : A) (s : set A) [finite s] :
--   (#finset a ∈ to_finset s) = (a ∈ s) :=
-- by rewrite [-to_set_to_finset at {2}]

theorem to_set_to_finset_of_not_finite {s : set A} (nfins : ¬ finite s) :
  finset.to_set (to_finset s) = ∅ :=
have to_finset s = finset.empty, from to_finset_of_not_finite nfins,
begin rw this, reflexivity end

-- theorem to_finset_to_set (s : finset A) : to_finset (finset.to_set s) = s :=
-- by rewrite [finset.eq_eq_to_set_eq, to_set_to_finset (finset.to_set s)]

-- theorem to_finset_eq_of_to_set_eq {s : set A} {t : finset A} (H : finset.to_set t = s) :
--   to_finset s = t :=
-- finset.eq_of_to_set_eq_to_set (by subst [s]; rewrite to_finset_to_set)


theorem finite_of_to_set_to_finset_eq {s : set A} (H : finset.to_set (to_finset s) = s) :
  finite s :=
by rewrite -H; apply finite_finset

attribute [instance]
theorem finite_empty : finite (∅ : set A) :=
by rewrite [-finset.to_set_empty]; apply finite_finset

attribute [instance]
theorem finite_insert (a : A) (s : set A) [finite s] : finite (set.insert a s) :=
exists.intro (finset.insert a (to_finset s))
(begin rw [-finset.to_set_insert, to_set_to_finset], end)


-- attribute [instance]
-- theorem finite_union (s t : set A) [finite s] [finite t] :
--   finite (s ∪ t) :=
-- exists.intro (to_finset s ∪ to_finset t)
-- (begin  end)

end set
