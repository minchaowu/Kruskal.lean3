import tools.super --.card
open classical nat function set tactic

namespace classical
universe variable u
variables {A : Type u} {p : A → Prop}

local attribute [instance] prop_decidable

theorem decidable.exists_not_of_not_forall [decidable (∃ x, ¬ p x)] [∀ x, decidable (p x)]
  (h : ¬ ∀ x, p x) : ∃ x, ¬ p x :=
decidable.by_contradiction
  (assume h₁, h (take x, decidable.by_contradiction (assume hnpx, h₁ ⟨x, hnpx⟩)))

-- theorem not_forall_of_exists_not (h : ∃ x, ¬ p x) : ¬ ∀ x, p x :=
-- assume h₁, match h with ⟨x, hnpx⟩ := hnpx (h₁ x) end
theorem exists_not_of_not_forall (h : ¬ ∀ x, p x) : ∃ x, ¬ p x :=
decidable.exists_not_of_not_forall h


end classical


theorem ne_nil_desturct {A : Type} {l : list A} : l ≠ [] → ∃ p : A × list A, l = p.1::p.2 := 
list.rec_on l (λ H, absurd rfl H) 
(λ a l' IH H, ⟨(a,l'),rfl⟩)
--(λ a l' IH H, ⟨a, ⟨l',rfl⟩⟩)

theorem or_resolve_right {a b : Prop} (h₁ : a ∨ b) (h₂ : ¬a) : b :=
by super

theorem or_resolve_left {a b : Prop} (h₁ : a ∨ b) (h₂ : ¬b) : a :=
by super
theorem lt_of_le_pred' {n m : ℕ} : n ≤ pred m →  n < m ∨ n = 0 :=
nat.rec_on m (λ h, or.elim (lt_or_eq_of_le h) (λ l, by super) (λ r, or.inr r)) 
(λ a ih h, or.inl (lt_succ_of_le h))

theorem lt_of_le_pred {n m : ℕ} : n ≤ pred m →  n < m ∨ m = 0 :=
nat.rec_on m (λ h, or.inr rfl) (λ a ih h, or.inl (lt_succ_of_le h))

theorem lt_succ_iff_le (m n : nat) : m < succ n ↔ m ≤ n :=
iff.intro le_of_lt_succ lt_succ_of_le

theorem eq_zero_or_eq_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
begin induction n, repeat { super } end

theorem exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : ∃k : ℕ, n = succ k :=
by super with eq_zero_or_eq_succ_pred

theorem succ_pred_of_pos {n : ℕ} (H : n > 0) : succ (pred n) = n :=
eq.symm (or_resolve_right (eq_zero_or_eq_succ_pred n) (ne.symm (ne_of_lt H)))

section
-- some facts about sets in the old library

parameter {X : Type}

theorem ext {a b : set X} (H : ∀x, x ∈ a ↔ x ∈ b) : a = b := funext (λ x, propext (H x))

theorem not_mem_empty (x : X) : ¬ (x ∈ (∅ : set X)) := λ H, H

lemma ne_empty_of_mem {s : set X} {x : X} (h : x ∈ s) : s ≠ ∅ :=
  begin intro hs, rewrite hs at h, apply not_mem_empty _ h end

theorem eq_empty_of_forall_not_mem {s : set X} (H : ∀ x, x ∉ s) : s = ∅ :=
ext (λ x, iff.intro (λ xs, absurd xs (H x)) (λ xe, absurd xe (not_mem_empty _)))

theorem exists_mem_of_ne_empty {s : set X} (H : s ≠ ∅) : ∃ x, x ∈ s :=
by_contradiction (λ H', H (eq_empty_of_forall_not_mem (forall_not_of_not_exists H')))

end

theorem image_nonempty {A B : Type} {f : A → B} {S : set A} (H : S ≠ ∅) : image f  S ≠ ∅ :=
have ∃ x, x ∈ S, from exists_mem_of_ne_empty H,
let ⟨s,h⟩ := this in
have f s ∈ image f S, from ⟨s, ⟨h,rfl⟩⟩,
ne_empty_of_mem this

section set
variable {α : Type}

theorem mem_univ (x : α) : x ∈ @univ α := trivial

theorem empty_ne_univ [h : inhabited α] : (∅ : set α) ≠ univ :=
assume H : ∅ = univ,
absurd (mem_univ (inhabited.default α)) (eq.rec_on H (not_mem_empty _))

theorem ne_empty_of_image_on_univ {A B : Type} (f : A → B) [inhabited A] : image f univ ≠ ∅ :=
have (∅ : set A) ≠ univ, from empty_ne_univ,
have ∃ a, a ∈ (univ : set A), from exists_mem_of_ne_empty (ne.symm this),
let ⟨a,h⟩ := this in
have f a ∈ image f univ, from exists.intro a (and.intro h rfl),
ne_empty_of_mem this

end set

section
-- the least number principle.

def complete_induction_on (n : ℕ) {p : ℕ → Prop} (h : ∀ n, (∀ m < n, p m) → p n) : p n :=
suffices ∀ n, ∀ m < n, p m, from this (succ n) _ (lt_succ_self n),
take n,
nat.rec_on n
  (take m, suppose m < 0, absurd this (not_lt_zero m))
  (take n,
    assume ih : ∀ m < n, p m,
    take m,
    suppose m < succ n,
    or.elim (lt_or_eq_of_le (le_of_lt_succ this))
      (ih m)
      (suppose m = n,
        begin rw this, apply h, exact ih end))

lemma wf_aux {A : set ℕ} (n : ℕ) : n ∈ A → ∃ a, a ∈ A ∧ ∀ b,  b ∈  A → a ≤ b := 
@complete_induction_on n (λ x, x ∈ A → ∃ a, a ∈  A ∧ ∀ b, b ∈ A → a ≤ b)
(λ k ih h, by_cases
(suppose ∃ m, m ∈ A ∧ m <k, let ⟨m, Hmem, Hlt⟩ := this in ih m Hlt Hmem)
(λ Hn, have ∀ m, m ∈  A →  ¬ m < k, by super, ⟨k,h,(λ m h, le_of_not_gt $ this m h)⟩))

theorem wf_of_le (S : set ℕ) (H : S ≠ ∅) : ∃ a, a ∈ S ∧ ∀ b, b ∈ S → a ≤ b :=
let ⟨n,Hn⟩ := exists_mem_of_ne_empty H in wf_aux n Hn

noncomputable definition least (S : set ℕ) (H : S ≠ ∅) : ℕ := some (wf_of_le S H)

theorem least_is_mem (S : set ℕ) (H : S ≠ ∅) : least S H ∈ S := 
let ⟨bound, Ha⟩ := some_spec (wf_of_le S H) in bound

theorem minimality {S : set ℕ} (neq : S ≠ ∅): ∀ x, x ∈ S → least S neq ≤ x := 
λ x Hx, let ⟨bound, Ha⟩ := some_spec (wf_of_le S neq) in Ha x Hx

end

-- lemma nonzero_card_of_finite {A : Type} {S : set A} (H : card S ≠ 0) : finite S :=
-- by_contradiction
-- (suppose ¬ finite S,
-- have card S = 0, from card_of_not_finite this,
-- H this)

-- lemma mem_not_in_diff {A : Type} {S : set A} {a : A} : a ∉ S \ insert a (∅ : set A) := 
-- assume h,
-- have a ∉ insert a (∅ : set A), from not_mem_of_mem_diff h,
-- this (mem_singleton a)

-- lemma insert_of_diff_singleton {A : Type} {S : set A} {a : A} (H : a ∈ S) : insert a (S \ insert a (∅ : set A)) = S :=
-- begin
-- apply eq_of_subset_of_subset,
-- intros x h, apply or.elim h, intro h1, simp [H, h1], -- simp,
-- intro hr, apply and.left hr,
-- intros x h', cases (decidable.em (x ∈ insert a (∅ : set A))),
-- apply or.inl, apply eq_of_mem_singleton, assumption,
-- apply or.inr, apply and.intro, repeat {assumption}
-- end

-- lemma union_of_diff_singleton {A : Type} {S : set A} {a : A} (H : a ∈ S) 
--   : S \ (insert a (∅ : set A)) ∪ (insert a (∅ : set A)) = S := 
-- begin
-- apply eq_of_subset_of_subset,
--   intros x h, apply or.elim h, intro hl, apply and.left hl,
--   intro hr, have h : x = a, from (mem_singleton_iff x a)^.mp hr,
--   rewrite h, simp,
--   intros x h', cases (decidable.em (x ∈ insert a (∅ : set A))),
--   apply or.inr, simp, apply or.inl, apply and.intro, repeat {simp}
-- end


-- lemma finite_singleton {A : Type} {a : A} : finite '{a} := 
-- have carda : card '{a} = 1, from card_singleton a,
-- have (1:ℕ) ≠ 0, from dec_trivial,
-- have card '{a} ≠ 0, by+ rewrite -carda at this;exact this,
-- nonzero_card_of_finite this

-- lemma sub_of_eq {A : Type} {S T: set A} (H : S = T) : S ⊆ T :=
-- have T ⊆ T, from subset.refl T,
-- by+ rewrite -H at this{1};exact this

-- theorem ne_empty_of_mem' {X : Type} {s : set X} {x : X} (H : x ∈ s) : s ≠ ∅ :=
-- begin intro Hs, rewrite Hs at H, apply not_mem_empty _ H end --this is on github
