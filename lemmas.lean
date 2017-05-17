import tools.super .card
open classical nat function set tactic

section
-- some facts about sets in the old library

parameter {X : Type}

-- theorem ext {a b : set X} (H : ∀x, x ∈ a ↔ x ∈ b) : a = b := funext (λ x, propext (H x))

theorem not_mem_empty (x : X) : ¬ (x ∈ (∅ : set X)) := λ H, H

theorem eq_empty_of_forall_not_mem {s : set X} (H : ∀ x, x ∉ s) : s = ∅ :=
set.ext (λ x, iff.intro (λ xs, absurd xs (H x)) (λ xe, absurd xe (not_mem_empty _)))

theorem exists_mem_of_ne_empty {s : set X} (H : s ≠ ∅) : ∃ x, x ∈ s :=
by_contradiction (λ H', H (eq_empty_of_forall_not_mem (forall_not_of_not_exists H')))

end


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

theorem minimality {S : set ℕ} {a : ℕ} {neq : S ≠ ∅}: ∀ x, x ∈ S → least S neq ≤ x := 
λ x Hx, let ⟨bound, Ha⟩ := some_spec (wf_of_le S neq) in Ha x Hx

end

lemma nonzero_card_of_finite {A : Type} {S : set A} (H : card S ≠ 0) : finite S :=
by_contradiction
(suppose ¬ finite S,
have card S = 0, from card_of_not_finite this,
H this)

lemma mem_not_in_diff {A : Type} {S : set A} {a : A} : a ∉ S \ insert a (∅ : set A) := 
assume h,
have a ∉ insert a (∅ : set A), from not_mem_of_mem_diff h,
this (mem_singleton a)

lemma insert_of_diff_singleton {A : Type} {S : set A} {a : A} (H : a ∈ S) : insert a (S \ insert a (∅ : set A)) = S :=
begin
apply eq_of_subset_of_subset,
intros x h, apply or.elim h, intro h1, simp [H, h1], -- simp,
intro hr, apply and.left hr,
intros x h', cases (decidable.em (x ∈ insert a (∅ : set A))),
apply or.inl, apply eq_of_mem_singleton, assumption,
apply or.inr, apply and.intro, repeat {assumption}
end

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
