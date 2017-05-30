import .logic .comb
open set classical

namespace finset

variable {A : Type}
variable [deceq : decidable_eq A]

definition to_set (s : finset A) : set A := λx, x ∈ s

-- def ts := @to_set A
instance finset_to_set_coe : has_coe (finset A) (set A) := ⟨to_set⟩

variables (s t : finset A) (x y : A)

theorem mem_eq_mem_to_set : x ∈ s = (x ∈ to_set s) := rfl

definition to_set.inj {s₁ s₂ : finset A} : to_set s₁ = to_set s₂ → s₁ = s₂ :=
λ h, ext (λ a, iff.of_eq (calc
  (a ∈ s₁) = (a ∈ to_set s₁) : mem_eq_mem_to_set _ _
       ... = (a ∈ to_set s₂) : by rw -h
       ... = (a ∈ s₂) : mem_eq_mem_to_set _ _))

-- A example
theorem mem_to_set_empty : (set.mem x (to_set empty)) = (mem x empty) := rfl
theorem to_set_empty : to_set empty = (∅:set A) := rfl

-- theorem mem_to_set_univ [h : fintype A] : (x ∈ to_set univ) = (x ∈ set.univ) :=
--   propext (iff.intro (assume H, trivial) (assume H, !mem_univ))
-- theorem to_set_univ [h : fintype A] : to_set univ = (set.univ : set A) := funext (λ x, !mem_to_set_univ)

-- instance : has_subset (finset A) := ⟨finset.subset⟩

theorem mem_to_set_upto (x n : ℕ) : x ∈ to_set (upto n) = (x ∈ {a | a < n}) := mem_upto_eq _ _
theorem to_set_upto (n : ℕ) : to_set (upto n) = {a | a < n} := funext (λ x, mem_to_set_upto _ _)

include deceq

theorem mem_to_set_insert : x ∈ insert y s = (x ∈ set.insert y s) := mem_insert_eq _ _ _

theorem to_set_insert : (set.insert y (to_set s)) = to_set (insert y s) := funext (λ x, eq.symm (mem_to_set_insert _ _ _))

theorem mem_to_set_union : x ∈ s ∪ t = (x ∈ to_set s ∪ to_set t) := mem_union_eq _ _ _
theorem to_set_union : to_set (s ∪ t) = to_set s ∪ to_set t := funext (λ x, mem_to_set_union _ _ _)

theorem mem_to_set_inter : x ∈ s ∩ t = (x ∈ to_set s ∩ to_set t) := mem_inter_eq _ _ _
theorem to_set_inter : to_set (s ∩ t) = to_set s ∩ to_set t := funext (λ x, mem_to_set_inter _ _ _)

theorem mem_to_set_diff : x ∈ s \ t = (x ∈ to_set s \ to_set t) := mem_diff_eq _ _ _
theorem to_set_diff : to_set (s \ t) = to_set s \ to_set t := funext (λ x, mem_to_set_diff _ _ _)

theorem mem_to_set_sep (p : A → Prop) [h : decidable_pred p] : x ∈ sep p s = (x ∈ set.sep p s) :=
  finset.mem_sep_eq _ _
theorem to_set_sep (p : A → Prop) [h : decidable_pred p] : to_set (sep p s) = set.sep p (to_set s) :=
  funext (λ x, mem_to_set_sep _ _ _)

theorem mem_to_set_image {B : Type} [h : decidable_eq B] (f : A → B) {s : finset A} {y : B} :
  y ∈ image f s = (y ∈ set.image f s) := mem_image_eq _ 
theorem to_set_image {B : Type} [h : decidable_eq B] (f : A → B) (s : finset A) :
to_set (image f s) = set.image f (to_set s) := funext (λ x, mem_to_set_image _)


/- relations -/

attribute [instance]
definition decidable_mem_to_set (x : A) (s : finset A) : decidable (x ∈ to_set s) :=
decidable_of_decidable_of_eq (decidable_mem _ _) (mem_eq_mem_to_set _ _)

theorem eq_of_to_set_eq_to_set {s t : finset A} (H : to_set s =  to_set t) : s = t :=
to_set.inj H

theorem eq_eq_to_set_eq : (s = t) = (to_set s = to_set t) :=
propext (iff.intro (assume H, H ▸ rfl) eq_of_to_set_eq_to_set)

-- #check quot.has_decidable_eq

attribute [instance]
definition decidable_to_set_eq (s t : finset A) : decidable (to_set s = to_set t) :=
decidable_of_decidable_of_eq (has_decidable_eq _ _) (eq_eq_to_set_eq _ _)

theorem subset_eq_to_set_subset (s t : finset A) : (s ⊆ t) = (to_set s ⊆ to_set t) :=
propext (iff.intro
  (assume H, take x xs, mem_of_subset_of_mem H xs)
  (assume H, subset_of_forall H))

-- attribute [instance]
-- definition decidable_subset [h : decidable_eq A] : ∀ (s t: finset A), decidable (s ⊆ t) :=
-- sorry

-- definition decidable_to_set_subset (s t : finset A) : decidable (to_set s ⊆ to_set t) :=
-- decidable_of_decidable_of_eq (decidable_subset _ _) (subset_eq_to_set_subset _ _)

/- bounded quantifiers -/

-- definition decidable_bounded_forall (s : finset A) (p : A → Prop) [h : decidable_pred p] :
--   decidable (∀ x ∈ to_set s, p x) :=
-- decidable_of_decidable_of_iff _ !all_iff_forall

-- definition decidable_bounded_existo_set (s : finset A) (p : A → Prop) [h : decidable_pred p] :
--   decidable (∃₀ x ∈ to_set s, p x) :=
-- decidable_of_decidable_of_iff _ !any_iff_exists

/- properties -/

-- theorem inj_on_to_set {B : Type} [h : decidable_eq B] (f : A → B) (s : finset A) :
--   inj_on f s = inj_on f (to_set s) :=
-- rfl

end finset
