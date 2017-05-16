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

-- A example
theorem mem_to_set_empty : (set.mem x (ts empty)) = (mem x empty) := rfl
theorem to_set_empty : ts empty = (∅:set A) := rfl

-- theorem mem_to_set_univ [h : fintype A] : (x ∈ ts univ) = (x ∈ set.univ) :=
--   propext (iff.intro (assume H, trivial) (assume H, !mem_univ))
-- theorem to_set_univ [h : fintype A] : ts univ = (set.univ : set A) := funext (λ x, !mem_to_set_univ)

-- instance : has_subset (finset A) := ⟨finset.subset⟩

theorem mem_to_set_upto (x n : ℕ) : x ∈ ts (upto n) = (x ∈ {a | a < n}) := mem_upto_eq _ _
theorem to_set_upto (n : ℕ) : ts (upto n) = {a | a < n} := funext (λ x, mem_to_set_upto _ _)

include deceq

theorem mem_to_set_insert : x ∈ insert y s = (x ∈ set.insert y s) := mem_insert_eq _ _ _

theorem to_set_insert : (set.insert y s) = (insert y s) := funext (λ x, eq.symm (mem_to_set_insert _ _ _))

theorem mem_to_set_union : x ∈ s ∪ t = (x ∈ ts s ∪ ts t) := mem_union_eq _ _ _
theorem to_set_union : ts (s ∪ t) = ts s ∪ ts t := funext (λ x, mem_to_set_union _ _ _)

theorem mem_to_set_inter : x ∈ s ∩ t = (x ∈ ts s ∩ ts t) := mem_inter_eq _ _ _
theorem to_set_inter : ts (s ∩ t) = ts s ∩ ts t := funext (λ x, mem_to_set_inter _ _ _)

theorem mem_to_set_diff : x ∈ s \ t = (x ∈ ts s \ ts t) := mem_diff_eq _ _ _
theorem to_set_diff : ts (s \ t) = ts s \ ts t := funext (λ x, mem_to_set_diff _ _ _)


theorem mem_to_set_sep (p : A → Prop) [h : decidable_pred p] : x ∈ sep p s = (x ∈ set.sep p s) :=
  finset.mem_sep_eq _ _
theorem to_set_sep (p : A → Prop) [h : decidable_pred p] : ↑(sep p s) = set.sep p s :=
  funext (λ x, mem_to_set_sep _ _ _)

theorem mem_to_set_image {B : Type} [h : decidable_eq B] (f : A → B) {s : finset A} {y : B} :
  y ∈ image f s = (y ∈ set.image f s) := mem_image_eq _ 
theorem to_set_image {B : Type} [h : decidable_eq B] (f : A → B) (s : finset A) :
↑(image f s) = set.image f s := funext (λ x, mem_to_set_image _)


/- relations -/

attribute [instance]
definition decidable_mem_to_set (x : A) (s : finset A) : decidable (x ∈ ts s) :=
decidable_of_decidable_of_eq (decidable_mem _ _) (mem_eq_mem_to_set _ _)

theorem eq_of_to_set_eq_to_set {s t : finset A} (H : ts s =  ts t) : s = t :=
to_set.inj H

theorem eq_eq_to_set_eq : (s = t) = (ts s = ts t) :=
propext (iff.intro (assume H, H ▸ rfl) eq_of_to_set_eq_to_set)

attribute [instance]
definition decidable_to_set_eq (s t : finset A) : decidable (ts s = ts t) :=
decidable_of_decidable_of_eq (has_decidable_eq _ _) (eq_eq_to_set_eq _ _)

theorem subset_eq_to_set_subset (s t : finset A) : (s ⊆ t) = (ts s ⊆ ts t) :=
propext (iff.intro
  (assume H, take x xs, mem_of_subset_of_mem H xs)
  (assume H, subset_of_forall H))

-- attribute [instance]
-- definition decidable_subset [h : decidable_eq A] : ∀ (s t: finset A), decidable (s ⊆ t) :=
-- sorry

-- definition decidable_to_set_subset (s t : finset A) : decidable (ts s ⊆ ts t) :=
-- decidable_of_decidable_of_eq (decidable_subset _ _) (subset_eq_to_set_subset _ _)

/- bounded quantifiers -/

-- definition decidable_bounded_forall (s : finset A) (p : A → Prop) [h : decidable_pred p] :
--   decidable (∀ x ∈ ts s, p x) :=
-- decidable_of_decidable_of_iff _ !all_iff_forall

-- definition decidable_bounded_exists (s : finset A) (p : A → Prop) [h : decidable_pred p] :
--   decidable (∃₀ x ∈ ts s, p x) :=
-- decidable_of_decidable_of_iff _ !any_iff_exists

/- properties -/

-- theorem inj_on_to_set {B : Type} [h : decidable_eq B] (f : A → B) (s : finset A) :
--   inj_on f s = inj_on f (ts s) :=
-- rfl

end finset
