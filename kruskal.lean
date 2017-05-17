import data.list tools.super
open nat function

-- lemmas of list

namespace list

variables {A B: Type} 

private theorem mem_cons (x : A) (l : list A) : x ∈ x :: l :=
or.inl rfl

def upto : ℕ → list ℕ
| 0      := []
| (succ n) := n :: upto n

theorem lt_of_mem_upto {n i : nat} : i ∈ upto n → i < n :=
nat.rec_on n (λ h, absurd h (not_mem_nil i)) 
(λ a ih h, or.elim h 
(begin intro l, rw l, apply lt_succ_self end) 
(λ r, lt_trans (ih r) (lt_succ_self a)))

theorem upto_succ (n : nat) : upto (succ n) = n :: upto n := rfl

theorem length_upto : ∀ n, length (upto n) = n
| 0        := rfl
| (succ n) := begin simp [upto_succ, length_cons, length_upto] end

#print filter

def dmap (p : A → Prop) [h : decidable_pred p] (f : Π a, p a → B) : list A → list B
| [] := []
| (a::l) := if P : (p a) then list.cons (f a P) (dmap l) else (dmap l)

/- map -/
theorem map_nil (f : A → B) : list.map f [] = [] := rfl

  section dmap

  variable {p : A → Prop}
  variable [h : decidable_pred p]
  include h
  variable {f : Π a, p a → B}

  lemma dmap_nil : dmap p f [] = [] := rfl

  lemma dmap_cons_of_pos {a : A} (P : p a) : ∀ l, dmap p f (a::l) = (f a P) :: dmap p f l :=
  λ l, dif_pos P

  lemma map_dmap_of_inv_of_pos {g : B → A} (Pinv : ∀ a (Pa : p a), g (f a Pa) = a) :
  ∀ {l : list A}, (∀ {{ a }}, a ∈ l → p a ) → map g (dmap p f l) = l

  | []     := assume Pl, by rewrite [dmap_nil, map_nil]
  | (a::l) := assume Pal, 
              have Pa : p a, from Pal (mem_cons _ _),
              have Pl : ∀ a, a ∈ l → p a,
                from take x Pxin, Pal (mem_cons_of_mem a Pxin), 
              by rewrite [dmap_cons_of_pos Pa, map_cons, Pinv, map_dmap_of_inv_of_pos Pl]

  end dmap

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

end fin

-- lemmas of bigops

namespace group_bigops

variables {A B : Type}

definition addf {A B : Type} [sgB : add_semigroup B] (f : A → B) : B → A → B :=
λ b a, b + f a

definition Suml [add_monoid B] (l : list A) (f : A → B) : B :=
list.foldl (addf f) 0 l

-- check add_monoid

end group_bigops

-- definitions

open group_bigops list fin

inductive finite_tree : Type
| cons : Π {n : ℕ},  (fin n → finite_tree) → finite_tree

namespace finite_tree

definition size : finite_tree → ℕ
| (@cons n ts) := Suml (fin.upto n) (λ i, size (ts i)) + 1

theorem exists_eq_cons_of_ne_nil {A : Type} {l : list A} : l ≠ [] → ∃ a, ∃ l', l = a::l' := 
list.rec_on l (λ H, absurd rfl H) (λ a l' IH H, ⟨a, ⟨l',rfl⟩⟩)

theorem pos_of_size (t : finite_tree) : 0 < size t :=
finite_tree.rec_on t (λ n ts ih, dec_trivial)

-- theorem pos_of_Suml {n : ℕ} (H : n ≠ 0) (ts : fin n → finite_tree) : 0 < Suml (upto n) (λ i, size (ts i)) :=
-- have upto n ≠ nil, from upto_ne_nil_of_ne_zero n H,
-- have ∃ a, ∃ l', fin.upto n = a::l', from exists_eq_cons_of_ne_nil this,
-- obtain a ha, from this,
-- obtain l' hl', from ha,
-- let f := λ i, size (ts i) in
-- have Suml (a::l') f = f a + Suml l' f, from Suml_cons f a l',
-- have f a > 0, from pos_of_size (ts a),
-- have f a + Suml l' f > 0, from add_pos_left this (Suml l' f),
-- by+ simp

-- theorem le_of_elt_Suml {n : ℕ} (ts : fin n → finite_tree) (k : fin n) : size (ts k) ≤ Suml (upto n) (λ i, size (ts i)) := -- what if n = 0?
-- have k ∈ upto n, from mem_upto n k,
-- have ∃s t, upto n = s ++ (k::t), from mem_split this,
-- obtain (s t) hst, from this,
-- have Suml (upto n) (λ i, size (ts i)) = Suml (s ++ (k::t)) (λ i, size (ts i)), by+ simp,
-- have Suml (s ++ (k::t)) (λ i, size (ts i)) = Suml s (λ i, size (ts i)) + Suml (k::t) (λ i, size (ts i)), from Suml_append s (k::t) (λ i, size (ts i)),
-- have Suml (k::t) (λ i, size (ts i)) = size (ts k) + Suml t (λ i, size (ts i)), from Suml_cons (λ i, size (ts i)) k t,
-- have size (ts k) ≤ size (ts k) + Suml t (λ i, size (ts i)), from le_add_right (size (ts k)) (Suml t (λ i, size (ts i))),
-- have le1 : size (ts k) ≤ Suml (k::t) (λ i, size (ts i)), by+ simp,
-- have Suml (k::t) (λ i, size (ts i)) ≤ Suml s (λ i, size (ts i)) + Suml (k::t) (λ i, size (ts i)), from le_add_left (Suml (k::t) (λ i, size (ts i))) (Suml s (λ i, size (ts i))),
-- have size (ts k) ≤ Suml s (λ i, size (ts i)) + Suml (k::t) (λ i, size (ts i)), from le.trans le1 this,
-- by+ simp

definition embeds : finite_tree → finite_tree → Prop
| (@cons 0 _) _              := true
| (@cons _ ts) (@cons 0 _)      := false
| (@cons _ ts) (@cons _ us) := (∃ j, embeds (cons ts) (us j)) ∨
                                  (∃ f, injective f ∧ ∀ i, embeds (ts i) (us (f i)))

/-
  -- here is a "hands on" definition of the same predicate:
  definition embeds (s t : finite_tree) : Prop :=
  (finite_tree.rec
    (finite_tree.rec true (λ m ss embss, false))
    (λ n ts embts,
      finite_tree.rec true (λ m ss embss,
        (∃ j, embts j (cons ss)) ∨ (∃ f, injective f ∧ ∀ i, embts (f i) (ss i)))))
  t s
-/

infix ` ≼ `:50 := embeds  -- \preceq

def node {ts : fin 0 → finite_tree} : finite_tree := @cons 0 ts

theorem node_embeds {ts : fin 0 → finite_tree} (t : finite_tree) : @cons 0 ts ≼ t :=
begin 
  cases t with n a, cases n,
  trivial, trivial
end

theorem not_cons_embeds_node {n : ℕ} {tt : fin 0 → finite_tree} (ts : fin (succ n) → finite_tree) : ¬ cons ts ≼ @node tt :=
λ h, begin cases n, exact h, exact h end

theorem not_embeds_empty {ts : fin 0 → finite_tree} (i : fin 0) (t : finite_tree) : ¬ t ≼ ts i :=
λ h, have i.val < 0, from i.is_lt, absurd this (not_lt_zero _)

-- curiously, with either definition above, this doesn't work with = and rfl
-- proposition cons_embeds_cons_iff {m n : ℕ} (ss : fin m → finite_tree) (ts : fin n → finite_tree) :
--   cons ss ≼ cons ts ↔ (∃ j, cons ss ≼ ts j) ∨ (∃ f, injective f ∧ ∀ i, ss i ≼ ts (f i)) :=
-- !iff.refl

theorem cons_embeds_cons_left {m n : ℕ} {ss : fin m → finite_tree} {ts : fin n → finite_tree}
    {j : fin n} (H : cons ss ≼ ts j) :
  cons ss ≼ cons ts :=
begin cases m, apply node_embeds, cases n, apply absurd H _, apply not_embeds_empty, apply or.inl (exists.intro j H) end

lemma foo {n : ℕ} {f : fin (succ n) → fin 0}  {ss : fin (succ n) → finite_tree} {ts : fin 0 → finite_tree} :
¬ ∀ a, ss a ≼ ts (f a) := λ h, have ss 0 ≼ ts (f 0), from h 0,
absurd this (by apply not_embeds_empty)

theorem cons_embeds_cons_right {m n : ℕ} {ss : fin m → finite_tree} {ts : fin n → finite_tree}
    {f : fin m → fin n} (injf : injective f) (Hf : ∀ i, ss i ≼ ts (f i)) :
  cons ss ≼ cons ts :=
begin cases m, apply node_embeds, cases n, 
apply absurd Hf _, apply foo,
apply or.inr (exists.intro f (and.intro injf Hf))
end

theorem cons_embeds_cons_dest {m n : ℕ} {ss : fin m → finite_tree} {ts : fin n → finite_tree}
    (H : cons ss ≼ cons ts) :
  (∃ j, cons ss ≼ ts j) ∨ (∃ f, injective f ∧ ∀ i, ss i ≼ ts (f i)) :=
sorry
-- begin cases m, apply or.inl, end

theorem embeds_refl (t : finite_tree) : t ≼ t :=
begin 
induction t with n a ih, 
cases n, trivial, apply cons_embeds_cons_right, 
apply injective_id, exact ih 
end

private def embeds_trans_aux : ∀ {u s t}, t ≼ u → s ≼ t → s ≼ u :=
λ u s t,finite_tree.rec_on s 
(λ sl ss ihs, 
nat.rec_on sl _ _) 

-- begin
-- intros u s t,
-- induction s with sl ss ihs,
-- cases sl,
-- {intros,apply node_embeds},
-- {induction t with tl ts iht,
--   cases tl,
--     {intros ht1 ht2, apply absurd ht2, apply not_cons_embeds_node},
--   induction u with ul us ihu,
--     cases ul,
--       intros hu1 hu2, apply absurd hu1, apply not_cons_embeds_node,
--     intros h1 h2,
--     apply cons_embeds_cons_right,-- or.,
--   -- induction h1,
-- },
-- --intros s t, --cases s with n ss,
-- end

-- private proposition embeds_trans_aux : ∀ {u s t}, t ≼ u → s ≼ t → s ≼ u :=
-- begin
--   intro u,
--   induction u with l us ihu,
--     intro s t, cases s with n ss,
--       intros, apply node_embeds,
--     cases t, repeat (intros; contradiction),
--   intro s t,
--     cases s with n ss,
--       intros, apply node_embeds,
--     cases t with m ts,
--       intros, contradiction,
--   intro H₁, cases (cons_embeds_cons_dest H₁) with H₁₁ H₁₂,
--     cases H₁₁ with i H₁₁, intro H₂,
--     have cons ss ≼ us i, from ihu _ H₁₁ H₂,
--     apply cons_embeds_cons_left this,
--   cases H₁₂ with f Hf, cases Hf with injf Hf,
--   intro H₂, cases (cons_embeds_cons_dest H₂) with H₂₁ H₂₂,
--     cases H₂₁ with j H₂₁,
--     have cons ss ≼ us (f j), from ihu _ (Hf j) H₂₁,
--     apply cons_embeds_cons_left this,
--   cases H₂₂ with g Hg, cases Hg with injg Hg,
--   apply cons_embeds_cons_right,
--   apply injective_compose injf injg,
--   intro i, apply ihu _ (Hf (g i)) (Hg i)
-- end

-- proposition embeds_trans {s t u : finite_tree} (H₁ : s ≼ t) (H₂ : t ≼ u) : s ≼ u :=
-- embeds_trans_aux H₂ H₁

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
