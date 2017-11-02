/-
Copyright (c) 2016 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu
-/

import tactic.finish
open classical nat function prod subtype

noncomputable theory

theorem lt_or_eq_of_lt_succ {n m : ℕ} (H : n < succ m) : n < m ∨ n = m := 
lt_or_eq_of_le (le_of_lt_succ H)

theorem and_of_not_imp {p q : Prop} (H : ¬ (p → ¬ q)) : p ∧ q := by finish

theorem existence_of_nat_gt (n : ℕ) : ∃ m, n < m := ⟨(succ n),(lt_succ_self n)⟩

namespace kruskal

class quasiorder (A : Type) extends has_le A :=
(refl : ∀ a, le a a)
(trans : ∀ {a b c}, le a b → le b c → le a c)
 
class wqo  (A : Type) extends quasiorder A :=
(is_good : ∀ f : ℕ → A,  ∃ i j, i < j ∧ le (f i) (f j))

def is_good {A : Type} (f : ℕ → A) (o : A → A → Prop) := ∃ i j : ℕ, i < j ∧ o (f i) (f j)

def prod_order {A B : Type} (o₁ : A → A → Prop) (o₂ : B → B → Prop) (s : A × B) (t : A × B) := 
o₁ (s.1) (t.1) ∧ o₂ (s.2) (t.2) 

instance qo_prod  {A B: Type} [o₁ : quasiorder A] [o₂ : quasiorder B] : quasiorder (A × B) :=
let op : A × B → A × B → Prop  := prod_order o₁.le o₂.le in
have refl : ∀ p : A × B, op p p, by intro; apply and.intro; repeat {apply quasiorder.refl},
have trans : ∀ a b c, op a b → op b c → op a c, from λ x y z h1 h2, 
⟨(quasiorder.trans h1^.left h2^.left), quasiorder.trans h1^.right h2^.right⟩,
show _, from quasiorder.mk (has_le.mk op) refl trans

def terminal {A : Type} (o : A → A → Prop) (f : ℕ → A) (m : ℕ) := 
∀ n, m < n → ¬ o (f m) (f n)

theorem lt_of_non_terminal {A : Type} {o : A → A → Prop} {f : ℕ → A} {m : ℕ} (H : ¬ @terminal _ o f m) : 
  ∃ n, m < n ∧ o (f m) (f n) :=
let ⟨n,h⟩ := exists_not_of_not_forall H in ⟨n,(and_of_not_imp h)⟩

section
parameter {A : Type}
parameter [o : wqo A]
parameter f : ℕ → A

  section
  parameter H : ∀ N, ∃ r, N < r ∧ terminal o.le f r
  
  def terminal_index (n : ℕ) : {x : ℕ // n < x ∧ terminal o.le f x} := 
  nat.rec_on n (let i := some (H 0) in ⟨i, (some_spec (H 0))⟩)
  (λ a rec_call, 
   let i' := rec_call.1, i := some (H i') in
   have p : i' < i ∧ terminal o.le f i, from some_spec (H i'),
   have a < i', from (rec_call.2)^.left,
   have succ a < i, from lt_of_le_of_lt this p^.left, 
   ⟨i, ⟨this,p^.right⟩⟩)

  lemma increasing_ti {n m : ℕ} : n < m → (terminal_index n).1 < (terminal_index m).1 :=
  nat.rec_on m (λ H, absurd H dec_trivial)
  (λ a ih lt,
   have disj : n < a ∨ n = a, from lt_or_eq_of_lt_succ lt,
   have (terminal_index a).1 < (terminal_index (succ a)).1, from
     (some_spec $ H (terminal_index a).1)^.left,
   or.elim disj (λ Hl, lt_trans (ih Hl) this) (λ Hr, by rw Hr;exact this))

  private def g (n : ℕ) := f (terminal_index n).1

  lemma terminal_g (n : ℕ) : terminal o.le g n :=   
  have ∀ n', (terminal_index n).1 < n' → ¬ (f (terminal_index n)^.1) ≤ (f n'), from ((terminal_index n).2)^.right,
  λ n' h, this (terminal_index n').1 (increasing_ti h)

  lemma bad_g : ¬ is_good g o.le := 
  have H1 : ∀ i j, i < j → ¬ (g i) ≤ (g j), from λ i j h, (terminal_g i) j h,
  λ h' : ∃ i j, i < j ∧  (g i) ≤ (g j),
  let ⟨i,j,h⟩ := h' in
  have ¬ (g i) ≤ (g j), from H1 i j h^.left,
  show _, from this h^.right

  lemma local_contradiction : false := bad_g (wqo.is_good g)

  end

theorem finite_terminal : ∃ N, ∀ r, N < r → ¬ terminal o.le f r := 
have ¬ ∀ N, ∃ r, N < r ∧ @terminal A o.le f r, by apply local_contradiction,
have ∃ N, ¬ ∃ r, N < r ∧ @terminal A o.le f r, by rw ←classical.not_forall_iff; exact this,
let ⟨n,h⟩ := this in 
have ∀ r, n < r → ¬ @terminal A o.le f r, from λ r lt neg, h ⟨r,⟨lt, neg⟩⟩,
⟨n,this⟩

end

section

parameters {A B : Type}
parameters [o₁ : wqo A] [o₂ : wqo B]

  section

  parameter f : ℕ → A × B

  theorem  finite_terminal_on_A : ∃ N, ∀ r, N < r → ¬ @terminal A o₁.le (fst ∘ f) r := 
  finite_terminal (fst ∘ f)

  def sentinel := some finite_terminal_on_A

  def h_helper (n : ℕ) : {x : ℕ // sentinel < x ∧ ¬ @terminal A o₁.le (fst ∘ f) x} :=
  nat.rec_on n
  (have ∃ m, sentinel < m, by apply existence_of_nat_gt,
  let i := some this in have ge : sentinel < i, from some_spec this,
  have ¬ @terminal A o₁.le (fst ∘ f) i, from (some_spec finite_terminal_on_A) i ge,
  have sentinel < i ∧ ¬ terminal o₁.le (fst ∘ f) i, from ⟨ge,this⟩,
  ⟨i, this⟩)
  (λ a rec_call, let i' := rec_call.1 in
  have lt' : sentinel < i', from (rec_call.2)^.left,
  have ¬ terminal o₁.le (fst ∘ f) i', from (rec_call.2)^.right,
  have ∃ n, i' < n ∧ ((fst ∘ f) i') ≤ ((fst ∘ f) n), from lt_of_non_terminal this,
  let i := some this in have i' < i, from (some_spec this)^.left,
  have lt : sentinel < i, from lt.trans lt' this,
  have ∀ r, sentinel < r → ¬ terminal o₁.le (fst ∘ f) r, from some_spec finite_terminal_on_A,
  have ¬ terminal o₁.le (fst ∘ f) i, from this i lt,
  have sentinel < i ∧ ¬ terminal o₁.le (fst ∘ f) i, from ⟨lt,this⟩,
  ⟨i,this⟩)

  private def h (n : ℕ) : ℕ := (h_helper n).1

  private lemma foo (a : ℕ) : h a < h (succ a) ∧ (fst ∘ f) (h a) ≤ (fst ∘ f) (h (succ a)) := 
  have ¬ terminal o₁.le (fst ∘ f) (h a), from ((h_helper a).2)^.right,
  have ∃ n, (h a) < n ∧ ((fst ∘ f) (h a)) ≤ ((fst ∘ f) n), from lt_of_non_terminal this,
  show _, from some_spec this

  theorem property_of_h {i j : ℕ} : i < j → (fst ∘ f) (h i) ≤ (fst ∘ f) (h j) :=
  nat.rec_on j (λ H, absurd H dec_trivial)
  (λ a IH lt,
  have H1 : (fst ∘ f) (h a) ≤ (fst ∘ f) (h (succ a)), from (foo a)^.right,
  have disj : i < a ∨ i = a, from lt_or_eq_of_lt_succ lt,
  or.elim disj (λ Hl, quasiorder.trans (IH Hl) H1) (λ Hr, by simp [Hr, H1])) 

  theorem increasing_h {i j : ℕ} : i < j → h i < h j :=
  nat.rec_on j
  (λ H, absurd H dec_trivial)
  (λ a ih lt,
  have H1 : (h a) < h (succ a), from (foo a)^.left,
  have disj : i < a ∨ i = a, from lt_or_eq_of_lt_succ lt,
  or.elim disj (λ Hl, lt_trans (ih Hl) H1) (λ Hr, by simp [Hr, H1]))

  theorem good_f : is_good f (prod_order o₁.le o₂.le) :=
  have ∃ i j : ℕ, i < j ∧ (snd ∘ f ∘ h) i ≤ (snd ∘ f ∘ h) j, from wqo.is_good (snd ∘ f ∘ h),
  let ⟨i,j,H⟩ := this in
  have (fst ∘ f) (h i) ≤ (fst ∘ f) (h j), from property_of_h H^.left,
  have Hr : (fst ∘ f) (h i) ≤ (fst ∘ f) (h j) ∧ (snd ∘ f) (h i) ≤ (snd ∘ f) (h j), from ⟨this, H^.right⟩,
  have h i < h j, from increasing_h H^.left,
  ⟨(h i), (h j), ⟨this,Hr⟩⟩

  end
  
theorem good_pairs (f : ℕ → A × B) : is_good f (prod_order o₁.le o₂.le) := good_f f

end

def wqo_prod {A B : Type} [o₁ : wqo A] [o₂ : wqo B] : wqo (A × B) :=
let op : A × B → A × B → Prop := prod_order o₁.le o₂.le in
have refl : ∀ p : A × B, op p p, from λ p, ⟨quasiorder.refl p.1,quasiorder.refl p.2⟩, -- by intro; apply and.intro;repeat {apply wqo.refl},
have trans : ∀ a b c, op a b → op b c → op a c, from λ a b c h1 h2, 
  ⟨quasiorder.trans h1^.left h2^.left, quasiorder.trans h1^.right h2^.right⟩,
show _, from wqo.mk ⟨⟨op⟩,refl,trans⟩ good_pairs

-- example {A B : Type} [o₁ : wqo A] [o₂ : wqo B] : (@wqo_prod A B _ _).le = prod_order o₁.le o₂.le := rfl

end kruskal
