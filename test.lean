import .higman
open nat function fin

#check @set.univ

theorem val_mapsto (n : ℕ) : maps_to val (@set.univ (fin n)) {i : ℕ | i < n} :=
take x, assume Ha, is_lt x

theorem refl_of_image_on_univ {A B: Type} (f : A → B) : set.image f (@set.univ A) = {b : B | ∃ x, f x = b} :=
have Hl : set.image f (@set.univ A) ⊆ {b : B | ∃ x, f x = b}, from 
  take x, assume Hx, 
  let ⟨i,h⟩ := Hx in exists.intro i (and.right h),
have {b : B | ∃ x, f x = b} ⊆ set.image f  (@set.univ A), from 
  take x, assume Hx, 
  let ⟨i,h⟩ := Hx in exists.intro i (and.intro trivial h),
set.subset.antisymm Hl this

inductive finite_tree : Type
| cons : Π {n : ℕ},  (fin n → finite_tree) → finite_tree

namespace finite_tree

definition embeds : finite_tree → finite_tree → Prop
| (@cons 0 _) _              := true
| (@cons _ ts) (@cons 0 _)      := false
| (@cons _ ts) (@cons _ us) := (∃ j, embeds (cons ts) (us j)) ∨
                                  (∃ f, injective f ∧ ∀ i, embeds (ts i) (us (f i)))

infix ` ≼ `:50 := embeds  -- \preceq

def node {ts : fin 0 → finite_tree} : finite_tree := @cons 0 ts

theorem node_embeds {ts : fin 0 → finite_tree} (t : finite_tree) : @node ts ≼ t :=
begin 
  cases t with n a, cases n,
  trivial, trivial
end



end finite_tree
