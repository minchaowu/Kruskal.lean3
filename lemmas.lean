open classical nat function set

section
-- the least number principle.

def complete_induction_on (n : ℕ) {p : ℕ → Prop} (h : ∀ n, (∀ m < n, p m) → p n) : p n :=
suffices ∀ n, ∀ m < n, p m, from this (succ n) _ (lt_succ_self n),
take n,
nat.induction_on n
  (take m, suppose m < 0, absurd this (not_lt_zero m))
  (take n,
    assume ih : ∀ m < n, p m,
    take m,
    suppose m < succ n,
    or.elim (lt_or_eq_of_le (le_of_lt_succ this))
      (ih m)
      (suppose m = n,
        begin rw this, apply h, exact ih end))

check @lt_or_eq_of_le
 
section
variables m n : ℕ 
variable A : set ℕ

example (H : ∃ a ∈ A, a < m) : ∃ b, b < m :=
let ⟨a, h, hle⟩ := H in ⟨a, hle⟩

end

lemma alt_of_wf {A : set ℕ} (n : ℕ) (H : n ∈ A): ∃ a ∈ A, ∀ b ∈ A, a ≤ b := 
@complete_induction_on n (λ k, ∃ a ∈ A, ∀ b ∈ A, a ≤ b)
(λ k ih, by_cases 
(suppose ∃ m ∈ A, m <n, let ⟨m, Hmem, Hlt⟩ := this in ih m Hlt)
(assume Hn, sorry)
) 

-- (take n, assume IH, assume ninA,  
-- by_cases
-- (suppose ∃ m ∈ A,  m < n, 
-- let ⟨m, Hm⟩ := this in
-- IH m (and.right Hm) (and.left Hm))
-- (suppose ¬ ∃ m ∈ A,  m < n, 
-- have ∀ m ∈ A,  ¬ m < n,from sorry, --by rewrite not_bounded_exists at this ; exact this,
-- have ∀ m, m ∈ A → n ≤ m, from sorry,
-- exists.intro n (and.intro ninA this)))

theorem wf_of_le (S : set ℕ) (H : S ≠ ∅) : ∃₀ a ∈ S, ∀₀ b ∈ S, a ≤ b :=
have ∃ x, x ∈ S, from exists_mem_of_ne_empty H,
obtain n (Hn : n ∈ S), from this,
alt_of_wf n Hn

noncomputable definition chooseleast (S : set ℕ) (H : S ≠ ∅) : ℕ := 
have ∃₀ a ∈ S, ∀₀ b ∈ S, a ≤ b, from wf_of_le S H,
some this

theorem least_is_mem (S : set ℕ) (H : S ≠ ∅) : chooseleast S H ∈ S := 
have H1 : ∃₀ a ∈ S, ∀₀ b ∈ S, a ≤ b, from wf_of_le S H,
have inS : some H1 ∈ S, from proof and.left (some_spec H1) qed,
have chooseleast S H = some H1, from rfl,
by+ rewrite -this at inS ; exact inS

theorem minimality {S : set ℕ} {a : ℕ} {H0 : S ≠ ∅} (H : a = chooseleast S H0): 
∀₀ x ∈ S, a ≤ x :=
take b, assume Hb,
have H1 : ∃₀ n ∈ S, ∀₀ m ∈ S, n ≤ m, from wf_of_le S H0,
have chooseleast S H0 = some H1, from rfl,
have eq : a = some H1, by+ rewrite this at H;exact H,
have ∀₀ m ∈ S, some H1 ≤ m, from proof and.right (some_spec H1) qed, 
have some H1 ≤ b, from this Hb,
by+ simp 

end

lemma nonzero_card_of_finite {A : Type} {S : set A} (H : card S ≠ 0) : finite S :=
by_contradiction
(suppose ¬ finite S,
have card S = 0, from card_of_not_finite this,
H this)

lemma mem_not_in_diff {A : Type} {S : set A} {a : A} : a ∉ S \ '{a} := 
suppose a ∈ S \ '{a},
have a ∉ '{a}, from not_mem_of_mem_diff this,
this (mem_singleton a)

lemma insert_of_diff_singleton {A : Type} {S : set A} {a : A} (H : a ∈ S) : insert a (S \ '{a}) = S :=
begin
apply eq_of_subset_of_subset,
  intros x h, apply or.elim h, intro, simp,
  intro hr, apply and.left hr,
  intro x h', cases (decidable.em (x ∈ '{a})),
  apply or.inl, apply eq_of_mem_singleton, simp,
  apply or.inr, apply and.intro, repeat simp
end

lemma union_of_diff_singleton {A : Type} {S : set A} {a : A} (H : a ∈ S) : S \ '{a} ∪ '{a} = S := 
begin
apply eq_of_subset_of_subset,
  intros x h, apply or.elim h, intro hl, apply and.left hl,
  intro hr, have x = a, from (and.left (mem_singleton_iff x a)) hr,
  rewrite this, simp,
  intros x h', cases (decidable.em (x ∈ '{a})),
  apply or.inr, simp, apply or.inl, apply and.intro, repeat simp
end

lemma finite_singleton {A : Type} {a : A} : finite '{a} := 
have carda : card '{a} = 1, from card_singleton a,
have (1:ℕ) ≠ 0, from dec_trivial,
have card '{a} ≠ 0, by+ rewrite -carda at this;exact this,
nonzero_card_of_finite this

lemma sub_of_eq {A : Type} {S T: set A} (H : S = T) : S ⊆ T :=
have T ⊆ T, from subset.refl T,
by+ rewrite -H at this{1};exact this

theorem ne_empty_of_mem' {X : Type} {s : set X} {x : X} (H : x ∈ s) : s ≠ ∅ :=
begin intro Hs, rewrite Hs at H, apply not_mem_empty _ H end --this is on github
