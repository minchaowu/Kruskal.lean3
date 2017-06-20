import data.list tools.super .library_dev.data.list.comb .library_dev.data.list.set 
open nat function tactic

-- lemmas of list

namespace list

variables {A B: Type} 

private theorem mem_cons (x : A) (l : list A) : x ∈ x :: l :=
or.inl rfl

-- def upto : ℕ → list ℕ
-- | 0      := []
-- | (succ n) := n :: upto n

-- theorem lt_of_mem_upto {n i : nat} : i ∈ upto n → i < n :=
-- nat.rec_on n (λ h, absurd h (not_mem_nil i)) 
-- (λ a ih h, or.elim h 
-- (begin intro l, rw l, apply lt_succ_self end) 
-- (λ r, lt_trans (ih r) (lt_succ_self a)))

-- theorem upto_succ (n : nat) : upto (succ n) = n :: upto n := rfl

-- theorem length_upto : ∀ n, length (upto n) = n
-- | 0        := rfl
-- | (succ n) := begin simp [upto_succ, length_cons, length_upto] end


/- map -/
theorem map_nil (f : A → B) : list.map f [] = [] := rfl

end list

open list

-- lemmas of fin

namespace fin

attribute [simp]
private theorem length_nil {A : Type} : length (@nil A) = 0 :=
rfl

lemma val_mk (n i : nat) (Plt : i < n) : fin.val (fin.mk i Plt) = i := rfl

def upto (n : ℕ) : list (fin n) :=
dmap (λ i, i < n) fin.mk (list.upto n)

lemma map_val_upto (n : nat) : map fin.val (upto n) = list.upto n := 
map_dmap_of_inv_of_pos (val_mk n) (@lt_of_mem_upto n) 

lemma length_upto (n : nat) : length (fin.upto n) = n :=
calc
  length (fin.upto n) = length (list.upto n) : (map_val_upto n ▸ eq.symm (length_map fin.val (upto n)))
  ... = n                    : length_upto n
 
lemma upto_ne_nil_of_ne_zero (n : nat) (Hn : n ≠ 0) : fin.upto n ≠ [] := 
begin 
  intro Hup, 
  apply Hn, 
  rewrite [-(@length_nil (fin n)), -Hup], 
  apply eq.symm (length_upto _)
end 

lemma mem_upto (n : nat) : ∀ (i : fin n), i ∈ upto n :=
take i, fin.rec_on i
  (take ival Piltn,
    have ival ∈ list.upto n, from mem_upto_of_lt Piltn,
mem_dmap Piltn this)

end fin

-- lemmas of bigops

-- namespace group_bigops

-- variables {A B : Type}

-- definition Suml (f : A → ℕ) : list A → ℕ 
-- | [] := 0
-- | (a :: ls) := f a + Suml ls

-- definition addf {A B : Type} [sgB : add_semigroup B] (f : A → B) : B → A → B :=
-- λ b a, b + f a

-- definition Suml [add_monoid B] (l : list A) (f : A → B) : B :=
-- list.foldl (addf f) 0 l

-- theorem Suml_nil (f : A → B) : Suml [] f = 0 := Prodl_nil f

-- -- check add_monoid

-- end group_bigops

-- definitions

section 

-- Suml

variables {A : Type}

definition Suml (f : A → ℕ) : list A → ℕ 
| [] := 0
| (a :: ls) := f a + Suml ls

theorem le_add_of_le {a b c : ℕ} : a ≤ b → a ≤ b + c :=
begin
induction c with n ih, intro,super, intro h2,
apply le_succ_of_le, exact ih h2
end

theorem le_of_mem_Suml {f : A → ℕ} {a : A} {l : list A} : 
a ∈ l → f a ≤ Suml f l :=
begin 
induction l with b ls ih, intro h, exact absurd h (not_mem_nil _),
dsimp [Suml], intro h, assert h' : a = b ∨ a ∈ ls, exact h,
cases h' with l r, rw l, apply le_add_right,
rw add_comm,apply le_add_of_le, exact ih r
end


end

open list fin

inductive finite_tree : Type
| cons : Π {n : ℕ},  (fin n → finite_tree) → finite_tree




namespace finite_tree

-- definition size : finite_tree → ℕ
-- | (@cons n ts) := Suml (fin.upto n) (λ i, size (ts i)) + 1
def size : finite_tree → ℕ
| (@cons n ts) := Suml (λ i, size (ts i)) (fin.upto n) + 1

-- theorem exists_eq_cons_of_ne_nil {A : Type} {l : list A} : l ≠ [] → ∃ a, ∃ l', l = a::l' := 
-- list.rec_on l (λ H, absurd rfl H) (λ a l' IH H, ⟨a, ⟨l',rfl⟩⟩)

theorem pos_of_size (t : finite_tree) : 0 < size t :=
finite_tree.rec_on t (λ n ts ih, dec_trivial)

theorem lt_of_size_branches_aux {n : ℕ} (ts : fin n → finite_tree) (k : fin n) : size (ts k) < Suml (λ i, size (ts i)) (upto n) + 1 := 
begin
assert kin : k ∈ upto n, exact mem_upto n k,
assert h : size (ts k) ≤ Suml (λ i, size (ts i)) (upto n), 
apply le_of_mem_Suml kin,
apply lt_succ_of_le, assumption
end

def embeds : finite_tree → finite_tree → Prop
| (@cons _ ts) (@cons _ us) := (∃ j, embeds (cons ts) (us j)) ∨
                                  (∃ f, injective f ∧ ∀ i, embeds (ts i) (us (f i)))

infix ` ≼ `:50 := embeds  -- \preceq

def node {ts : fin 0 → finite_tree} : finite_tree := @cons 0 ts

def {u} fin_zero_absurd {α : Sort u} (i : fin 0) : α :=
absurd i.2 (not_lt_zero i.1)

theorem node_embeds {ts : fin 0 → finite_tree} (t : finite_tree) : @cons 0 ts ≼ t :=
begin 
  induction t with n a ih,
  dsimp [embeds],  
  pose f : fin 0 → fin n := λ i : fin 0, fin_zero_absurd i,
  apply or.inr,
  existsi f,
  split,
    intros i j hij, exact fin_zero_absurd i,
  intro i, exact fin_zero_absurd i
end

theorem not_embeds_node {n : ℕ} {ts : fin (succ n) → finite_tree} 
  {tt : fin 0 → finite_tree}: ¬ cons ts ≼ cons tt := 
begin 
  intro h,
  dsimp [embeds] at h,
  cases h with h₁ h₂,
  { cases h₁ with i hi, exact fin_zero_absurd i },  
  cases h₂ with f hf, exact fin_zero_absurd (f ⟨0, zero_lt_succ _⟩)
end

theorem cons_embeds_cons_left {m n : ℕ} {ss : fin m → finite_tree} {ts : fin n → finite_tree}
    {j : fin n} (H : cons ss ≼ ts j) :
  cons ss ≼ cons ts :=
begin 
cases m, 
apply node_embeds, cases n,
exact fin_zero_absurd j,
apply or.inl (exists.intro j H) 
end

theorem cons_embeds_cons_right {m n : ℕ} {ss : fin m → finite_tree} {ts : fin n → finite_tree}
    {f : fin m → fin n} (injf : injective f) (Hf : ∀ i, ss i ≼ ts (f i)) :
  cons ss ≼ cons ts :=
begin cases m, apply node_embeds, cases n, 
exact fin_zero_absurd (f 0),
apply or.inr (exists.intro f (and.intro injf Hf))
end

theorem embeds_refl (t : finite_tree) : t ≼ t :=
begin 
induction t with n a ih, 
cases n, apply node_embeds,
apply cons_embeds_cons_right, 
apply injective_id, exact ih 
end

theorem embeds_trans_aux : ∀ {u s t}, t ≼ u → s ≼ t → s ≼ u :=
begin
  intro u,
  induction u with ul us ihu,
    intros s t, cases s with sl ss,
    cases t with tl ts,
  intro H₁, dsimp [embeds] at H₁, cases H₁ with H₁₁ H₁₂,
  cases H₁₁ with i H₁₁, intro H₂,
    apply cons_embeds_cons_left (ihu _ H₁₁ H₂),
    cases H₁₂ with f Hf, cases Hf with injf Hf,
  intro H₂, dsimp [embeds] at H₂, cases H₂ with H₂₁ H₂₂,
    cases H₂₁ with j H₂₁,
    apply cons_embeds_cons_left (ihu _ (Hf j) H₂₁),
    cases H₂₂ with g Hg, cases Hg with injg Hg,
    apply cons_embeds_cons_right,
    apply injective_comp injf injg,
    intro i, apply ihu _ (Hf (g i)) (Hg i)
end

theorem embeds_trans {s t u : finite_tree} (H₁ : s ≼ t) (H₂ : t ≼ u) : s ≼ u :=
embeds_trans_aux H₂ H₁

-- proposition cons_embeds_iff {m : ℕ} (ss : fin m → finite_tree) (t : finite_tree) :
--   cons ss ≼ t ↔ ∃ n (ts : fin n → finite_tree), t = cons ts ∧
--                   ((∃ j, cons ss ≼ ts j) ∨ (∃ f, injective f ∧ ∀ i, ss i ≼ ts (f i))) :=
-- begin
--   apply iff.intro,
--     intro H, cases t with n ts,
--       contradiction,
--     existsi n, existsi ts, split, reflexivity, apply cons_embeds_cons_dest H,
--   intro H, cases H with n H, cases H with ts H, cases H with teq H,
--   rewrite teq, exact H
-- end

end finite_tree
