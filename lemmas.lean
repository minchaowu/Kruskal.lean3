import data.set.basic
open classical nat function set tactic

section
-- the least number principle.

lemma wf_aux {A : set ℕ} (n : ℕ) : n ∈ A → ∃ a, a ∈ A ∧ ∀ b,  b ∈  A → a ≤ b := 
@nat.strong_induction_on (λ x, x ∈ A → ∃ a, a ∈  A ∧ ∀ b, b ∈ A → a ≤ b) n
(λ k ih h, by_cases
(λ pos : ∃ m, m ∈ A ∧ m < k, let ⟨m, Hmem, Hlt⟩ := pos in ih m Hlt Hmem)
(λ _, have ∀ m, m ∈  A →  ¬ m < k, by finish, ⟨k, h, (λ m h, le_of_not_gt $ this m h)⟩))

theorem well_founded_le (S : set ℕ) (H : S ≠ ∅) : ∃ a, a ∈ S ∧ ∀ b, b ∈ S → a ≤ b :=
let ⟨n, Hn⟩ := exists_mem_of_ne_empty H in wf_aux n Hn

noncomputable def least (S : set ℕ) (H : S ≠ ∅) : ℕ := some (well_founded_le S H)

theorem mem_least (S : set ℕ) (H : S ≠ ∅) : least S H ∈ S := 
let ⟨bound, Ha⟩ := some_spec (well_founded_le S H) in bound

theorem minimality {S : set ℕ} (neq : S ≠ ∅): ∀ x, x ∈ S → least S neq ≤ x := 
λ x Hx, let ⟨bound, Ha⟩ := some_spec (well_founded_le S neq) in Ha x Hx

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
