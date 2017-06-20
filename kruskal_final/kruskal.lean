import .higman
open nat function prod set fin classical subtype

namespace list
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


def upto : nat → list nat
| 0     := []
| (n+1) := n :: upto n

def dmap {α β : Type} (p : α → Prop) [h : decidable_pred p] (f : Π a, p a → β) : list α → list β
| []       := []
| (a::l)   := if P : (p a) then cons (f a P) (dmap l) else (dmap l)

theorem mem_upto_succ_of_mem_upto {n i : nat} : i ∈ upto n → i ∈ upto (succ n) :=
assume i, mem_cons_of_mem _ i
theorem mem_upto_of_lt : ∀ ⦃n i : nat⦄, i < n → i ∈ upto n
| 0        := λ i h, absurd h (not_lt_zero i)
| (succ n) := λ i h,
begin
  cases nat.lt_or_eq_of_le (le_of_lt_succ h) with ilt ieq,
  { apply mem_upto_succ_of_mem_upto, apply mem_upto_of_lt ilt },
  simp [ieq], super
end

section dmap
variables {α β : Type}
variable {p : α → Prop}
variable [h : decidable_pred p]
include h
variable {f : Π a, p a → β}

lemma dmap_nil : dmap p f [] = [] := rfl
lemma dmap_cons_of_pos {a : α} (P : p a) : ∀ l, dmap p f (a::l) = (f a P) :: dmap p f l :=
      λ l, dif_pos P
lemma dmap_cons_of_neg {a : α} (P : ¬ p a) : ∀ l, dmap p f (a::l) = dmap p f l :=
      λ l, dif_neg P

lemma mem_dmap : ∀ {l : list α} {a} (Pa : p a), a ∈ l → (f a Pa) ∈ dmap p f l
| []     := take a Pa Pinnil, absurd Pinnil (not_mem_nil _)
| (a::l) := take b Pb Pbin, or.elim (eq_or_mem_of_mem_cons Pbin)
              (assume Pbeqa, begin
                rw [eq.symm Pbeqa, dmap_cons_of_pos Pb],
                apply mem_cons_self
              end)
              (assume Pbinl,
                if pa : p a then
                  begin
                    rw [dmap_cons_of_pos pa],
                    apply mem_cons_of_mem,
                    exact mem_dmap Pb Pbinl
                  end
                else
                  begin
                    rw [dmap_cons_of_neg pa],
                    exact mem_dmap Pb Pbinl
                   end)


end dmap

end list

namespace fin
open list
attribute [simp]
private theorem length_nil {A : Type} : length (@nil A) = 0 :=
rfl

lemma val_mk (n i : nat) (Plt : i < n) : fin.val (fin.mk i Plt) = i := rfl

def upto (n : ℕ) : list (fin n) :=
dmap (λ i, i < n) fin.mk (list.upto n)

lemma mem_upto (n : nat) : ∀ (i : fin n), i ∈ upto n :=
take i, fin.rec_on i
  (take ival Piltn,
    have ival ∈ list.upto n, from mem_upto_of_lt Piltn,
mem_dmap Piltn this)

end fin

namespace kruskal


-- universe u

inductive finite_tree (Q : Type): Type
| cons : Q → list finite_tree → finite_tree

open finite_tree

-- def embeds' {Q : Type} [has_le Q] : finite_tree Q → finite_tree Q → Prop
-- | (cons a l) (cons b l') := sorry -- ∃ l₁, l₁ ∈ l' ∧ embeds' (cons a l) l₁  


open finite_tree list function

#check @sublist'

inductive embeds {Q : Type} [has_le Q] : finite_tree Q → finite_tree Q → Prop
| embeds_subtree (t t' : finite_tree Q) (a : Q) (l' : list (finite_tree Q)) : 
      t' ∈ l' → embeds t t' → embeds t (cons a l')
| embeds_par (a a' : Q) (l l' : list (finite_tree Q)) : a ≤ a' →  @sublist' _ ⟨embeds⟩ l l' → embeds (cons a l) (cons a' l') 
  


-- def size' {Q : Type} : finite_tree Q → ℕ
-- | (cons a l) := 




end kruskal


-- inductive finite_tree (Q : Type): Type
-- | cons : Π {n : ℕ},  Q → (fin n → finite_tree) → finite_tree

-- open finite_tree

-- def size {Q : Type} : finite_tree Q → ℕ
-- | (@cons ._ n _ ts) := list.Suml (λ i, size (ts i)) (fin.upto n) + 1

-- theorem lt_of_size_branches_aux {Q : Type} {n : ℕ} (ts : fin n → finite_tree Q) (k : fin n) : 
-- size (ts k) < list.Suml (λ i, size (ts i)) (fin.upto n) + 1 := 
-- begin
-- assert kin : k ∈ fin.upto n, exact fin.mem_upto n k,
-- assert h : size (ts k) ≤ list.Suml (λ i, size (ts i)) (fin.upto n), 
-- apply list.le_of_mem_Suml kin,
-- apply lt_succ_of_le, assumption
-- end

-- def embeds {Q : Type} [has_le Q] : finite_tree Q → finite_tree Q → Prop
-- | (@cons ._ n a ts) (@cons ._ m b us) :=  (∃ j, embeds (cons a ts) (us j)) ∨                                             (a ≤ b ∧ ∃ f, injective f ∧ ∀ i, embeds (ts i) (us (f i)))

-- infix ` ≼ `:50 := embeds  -- \preceq

-- def {u} fin_zero_absurd {α : Sort u} (i : fin 0) : α :=
-- absurd i.2 (not_lt_zero i.1)

-- -- def branches_aux {Q : Type} {n : ℕ} (ts : fin n → finite_tree Q) : set (finite_tree Q × ℕ) := 
-- -- {x : finite_tree Q × ℕ | ∃ a : fin n, ts a = x.1 ∧ val a = x.2}

-- def branches_aux {Q : Type} {n : ℕ} (ts : fin n → finite_tree Q) : list (finite_tree Q) := 
-- list.map ts (fin.upto n)

-- definition branches {Q : Type} : finite_tree Q → list (finite_tree Q)
-- | (@cons ._ n _ ts) := branches_aux ts

-- -- definition branches {Q : Type} : finite_tree Q → set (finite_tree Q × ℕ) 
-- -- | (@cons ._ n _ ts) := branches_aux ts

-- section
-- variable {Q : Type}
-- variable [quasiorder Q]

-- theorem cons_embeds_cons_left {m n : ℕ} {a b : Q} {ss : fin m → finite_tree Q} {ts : fin n → finite_tree Q}
--     {j : fin n} (H : cons a ss ≼ ts j) :
--   cons a ss ≼ cons b ts :=
-- begin 
-- dsimp [embeds], apply or.inl,existsi j, exact H
-- end

-- theorem cons_embeds_cons_right {m n : ℕ} {a b : Q} {ss : fin m → finite_tree Q} {ts : fin n → finite_tree Q}
--     {f : fin m → fin n} (H : a ≤ b) (injf : injective f) (Hf : ∀ i, ss i ≼ ts (f i)) :
--   cons a ss ≼ cons b ts :=
-- begin 
-- dsimp [embeds], apply or.inr, split, exact H,
-- existsi f, apply (and.intro injf Hf)
-- end

-- theorem embeds_refl (t : finite_tree Q) : t ≼ t :=
-- begin 
-- induction t with n b ts ih, 
-- dsimp [embeds], apply or.inr, split, apply quasiorder.refl,
-- existsi id, apply and.intro, exact injective_id, exact ih
-- end

-- theorem embeds_trans_aux : ∀ {u s t : finite_tree Q}, t ≼ u → s ≼ t → s ≼ u :=
-- begin
-- intro u,
-- induction u with ul ua us ihu,
--   intros s t, cases s with sl sa ss,
--   cases t with tl ta ts,
-- intro H₁, dsimp [embeds] at H₁, cases H₁ with H₁₁ H₁₂,
-- cases H₁₁ with i H₁₁, intro H₂,
--   apply cons_embeds_cons_left (ihu _ H₁₁ H₂),
--   cases H₁₂ with hab H₁₂r, cases H₁₂r with f Hf,
--   cases Hf with injf Hf,
-- intro H₂, dsimp [embeds] at H₂, cases H₂ with H₂₁ H₂₂,
-- cases H₂₁ with j H₂₁,
-- apply cons_embeds_cons_left (ihu _ (Hf j) H₂₁),
-- cases H₂₂ with Hab H₂₂r, cases H₂₂r with g Hg,
-- cases Hg with injg Hg,
-- apply cons_embeds_cons_right,
-- apply quasiorder.trans Hab hab,
-- apply injective_comp injf injg,
-- intro i, apply ihu _ (Hf (g i)) (Hg i)
-- end

-- theorem embeds_trans {s t u : finite_tree Q} (H₁ : s ≼ t) (H₂ : t ≼ u) : s ≼ u :=
-- embeds_trans_aux H₂ H₁

-- theorem embeds_of_branches {t : finite_tree Q} {T : finite_tree Q} : t ∈ (branches T) → t ≼ T := 
-- begin
-- cases T with n a ts,
-- cases t with tn ta tss,
-- intro H, dsimp [embeds],
-- dsimp [branches] at H,
-- dsimp [branches_aux] at H,
-- end

-- end

-- theorem lt_of_size_of_branches {Q : Type} {t : finite_tree Q × ℕ} {T : finite_tree Q} : t ∈ branches T → size t.1 < size T :=
-- begin 
-- cases T with n a ts,
-- intro h,
-- assert h' : ∃ i, ts i = t.1, cases h with b hb, 
--  {exact exists.intro b hb^.left},
-- cases h' with c hc, rw -hc, apply lt_of_size_branches_aux
-- end

-- noncomputable theory

-- section
-- parameter {Q : Type}
-- parameter [wqo Q]
-- parameter H : ∃ f : ℕ → finite_tree Q, ¬ is_good f embeds

-- def mbs_of_finite_tree := minimal_bad_seq size H 

-- theorem bad_mbs_finite_tree : ¬ is_good mbs_of_finite_tree embeds := badness_of_mbs size H

-- def seq_branches_of_mbs_tree (n : ℕ) : set (finite_tree Q × ℕ) := branches (mbs_of_finite_tree n)

-- def mbs_tree : Type := {t : finite_tree Q × ℕ // ∃ i, t ∈ seq_branches_of_mbs_tree i}

-- def embeds' (t : mbs_tree) (s : mbs_tree) : Prop := t.val.1 ≼ s.val.1

-- theorem embeds'_refl (t : mbs_tree) : embeds' t t := embeds_refl t.val.1

-- theorem embeds'_trans (a b c : mbs_tree) : embeds' a b → embeds' b c → embeds' a c :=
-- λ H₁ H₂, embeds_trans H₁ H₂

--   section

--   parameter H' : ∃ f, ¬ is_good f embeds'

--   def R : ℕ → mbs_tree := some H'

--   definition family_index (n : ℕ) : ℕ := some ((R n).2) 

--   definition index_set_of_mbs_tree : set ℕ := image family_index  univ

--   lemma index_ne_empty : index_set_of_mbs_tree ≠ ∅ := ne_empty_of_image_on_univ family_index

--   definition least_family_index := least index_set_of_mbs_tree index_ne_empty

--   lemma exists_least : ∃ i, family_index i = least_family_index :=
--   have least_family_index ∈ index_set_of_mbs_tree, from least_is_mem index_set_of_mbs_tree index_ne_empty,
--   let ⟨i,h⟩ := this in
--   ⟨i, h^.right⟩

--   definition least_index : ℕ := some exists_least

--   definition Kruskal's_g (n : ℕ) : mbs_tree := R (least_index + n)

--   definition Kruskal's_h (n : ℕ) : ℕ :=  family_index (least_index + n)

--   theorem bad_Kruskal's_g : ¬ is_good Kruskal's_g embeds' :=
--   suppose is_good Kruskal's_g embeds',
--   let ⟨i,j,hij⟩ := this in
--   have Hr : embeds' (Kruskal's_g i) (Kruskal's_g j), from hij^.right,
--   have least_index + i < least_index + j, from add_lt_add_left hij^.left _,
--   have is_good R embeds', from ⟨least_index + i, ⟨least_index + j,⟨this, Hr⟩⟩⟩,
--   (some_spec H') this

--   theorem Kruskal's_Hg : ¬ is_good (fst ∘ (val ∘ Kruskal's_g)) embeds := bad_Kruskal's_g

--   theorem trans_of_Kruskal's_g {i j : ℕ} (H1 : mbs_of_finite_tree i ≼ (Kruskal's_g j).val.1) : 
--   mbs_of_finite_tree i ≼ mbs_of_finite_tree (Kruskal's_h j) := 
--   have (Kruskal's_g j).val ∈ branches (mbs_of_finite_tree (Kruskal's_h j)), from some_spec (Kruskal's_g j).2,
--   have (Kruskal's_g j).val.1 ≼ mbs_of_finite_tree (Kruskal's_h j), from embeds_of_branches this,
--   embeds_trans H1 this

--   theorem size_elt_Kruskal's_g_lt_mbs_finite_tree (n : ℕ) : size (Kruskal's_g n).val.1 < size (mbs_of_finite_tree (Kruskal's_h n)) := 
--   lt_of_size_of_branches (some_spec (Kruskal's_g n).2)

--   theorem Kruskal's_Hbp : size (Kruskal's_g 0).val.1 < size (mbs_of_finite_tree (Kruskal's_h 0)) := size_elt_Kruskal's_g_lt_mbs_finite_tree 0

--   lemma family_index_in_index_of_mbs_tree (n : ℕ) : Kruskal's_h n ∈ index_set_of_mbs_tree :=
--   have Kruskal's_h n = family_index (least_index + n), from rfl,
--   ⟨(least_index + n),⟨trivial,rfl⟩⟩

--   theorem Kruskal's_Hh (n : ℕ) : Kruskal's_h 0 ≤ Kruskal's_h n :=
--   have Kruskal's_h 0 = family_index least_index, from rfl,--by simph,
--   have family_index least_index = least_family_index, from some_spec exists_least,
--   have Kruskal's_h 0 = least_family_index, by simph,
--   begin rw this, apply minimality, apply family_index_in_index_of_mbs_tree end

--   theorem Kruskal's_H : ∀ i j, mbs_of_finite_tree i ≼ (Kruskal's_g (j - Kruskal's_h 0)).val.1 → mbs_of_finite_tree i ≼ mbs_of_finite_tree (Kruskal's_h (j - Kruskal's_h 0)) := λ i j, λ H1, trans_of_Kruskal's_g H1

--   definition Kruskal's_comb_seq (n : ℕ) : finite_tree Q := @comb_seq_with_mbs _ embeds (fst ∘ (val ∘ Kruskal's_g)) Kruskal's_h size H n

--   theorem Kruskal's_local_contradiction : false := local_contra_of_comb_seq_with_mbs Kruskal's_h size Kruskal's_Hh H Kruskal's_Hg Kruskal's_H Kruskal's_Hbp

--   end

-- theorem embeds'_is_good : ∀ f, is_good f embeds' := 
-- by_contradiction
-- (suppose ¬ ∀ f, is_good f embeds',
--  have ∃ f, ¬ is_good f embeds', from classical.exists_not_of_not_forall this,
--  Kruskal's_local_contradiction this)

-- instance wqo_mbs_tree : wqo mbs_tree :=
-- ⟨⟨⟨embeds'⟩,embeds'_refl,embeds'_trans⟩,embeds'_is_good⟩

-- def wqo_list_mbs_tree : wqo (list mbs_tree) := wqo_list

-- def sub : list mbs_tree → list mbs_tree → Prop := wqo_list_mbs_tree.le 

-- theorem good_list_mbs_tree : ∀ f, is_good f sub := wqo_list_mbs_tree.is_good

-- definition elt_mirror (n : ℕ) : set mbs_tree := {x : mbs_tree | x.1 ∈ seq_branches_of_mbs_tree n}

-- theorem mirror_refl_left (x : mbs_tree) (n : ℕ) : x ∈ elt_mirror n → x.1 ∈ seq_branches_of_mbs_tree n := λ Hx, Hx

-- theorem mirror_refl_right (x : mbs_tree) (n : ℕ) : x.1 ∈ seq_branches_of_mbs_tree n → x ∈ elt_mirror n := λ Hx, Hx

-- definition mirror (n : ℕ) : list mbs_tree := _

-- #check list

-- end


-- end kruskal
