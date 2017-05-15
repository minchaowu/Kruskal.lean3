import .logic .comb 
open set classical

namespace finset

variable {A : Type}
variable [deceq : decidable_eq A]

definition to_set (s : finset A) : set A := λx, x ∈ s

def ts := @to_set A
instance finset_to_set_coe : has_coe (finset A) (set A) := ⟨ts⟩

variables (s t : finset A) (x y : A)

theorem mem_eq_mem_to_set : x ∈ s = (x ∈ ts s) := rfl

definition to_set.inj {s₁ s₂ : finset A} : ts s₁ = ts s₂ → s₁ = s₂ :=
λ h, ext (λ a, iff.of_eq (calc
  (a ∈ s₁) = (a ∈ ts s₁) : mem_eq_mem_to_set _ _
       ... = (a ∈ ts s₂) : by rw -h
       ... = (a ∈ s₂) : mem_eq_mem_to_set _ _))

theorem to_set_empty : ts empty = (∅:set A) := rfl

include deceq

theorem mem_to_set_insert : x ∈ insert y s = (x ∈ set.insert y s) := mem_insert_eq _ _ _

theorem to_set_insert : (set.insert y s) = (insert y s) := funext (λ x, eq.symm (mem_to_set_insert _ _ _))

end finset
