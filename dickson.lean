/-
Copyright (c) 2016 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu
-/

import tools.super
open classical nat function prod subtype super

noncomputable theory

theorem lt_or_eq_of_lt_succ {n m : ℕ} (H : n < succ m) : n < m ∨ n = m := 
lt_or_eq_of_le (le_of_lt_succ H)

theorem and_of_not_imp {p q : Prop} (H : ¬ (p → ¬ q)) : p ∧ q := by super

theorem not_not_elim {a : Prop} : ¬¬a → a := by_contradiction

theorem exists_not_of_not_forall {A : Type} {p : A → Prop} (H : ¬∀x, p x) : ∃x, ¬p x :=
by_contradiction (λ neg, have ∀ x, ¬ ¬ p x, from forall_not_of_not_exists neg,
show _, from H (λ x, not_not_elim (this x)))

theorem existence_of_nat_gt (n : ℕ) : ∃ m, n < m := ⟨(succ n),(lt_succ_self n)⟩

namespace kruskal

structure [class] quasiorder (A : Type) extends has_le A : Type :=
(refl : ∀ a, le a a)
(trans : ∀ {a b c}, le a b → le b c → le a c)

theorem le_refl {A : Type} [quasiorder A] (a : A) : a ≤ a := 
quasiorder.refl a

theorem le_trans {A : Type} [H : quasiorder A] {a b c : A} (H₁ : a ≤ b) (H₂ : b ≤ c) : a ≤ c := quasiorder.trans H₁ H₂
 
structure [class] wqo  (A : Type) extends quasiorder A : Type :=
(is_good : ∀ f : ℕ → A,  ∃ i j : ℕ, i < j ∧ le (f i) (f j))

def is_good {A : Type} (f : ℕ → A) (o : A → A → Prop) := ∃ i j : ℕ, i < j ∧ o (f i) (f j)

def o_for_pairs {A B : Type} (o₁ : A → A → Prop) (o₂ : B → B → Prop) (s : A × B) (t : A × B) := 
o₁ (s^.1) (t^.1) ∧ o₂ (s^.2) (t^.2) 

instance qo_prod  {A B: Type} [o₁ : quasiorder A] [o₂ : quasiorder B] : quasiorder (A × B) :=
let op : A × B → A × B → Prop  := o_for_pairs quasiorder.le quasiorder.le in
have refl : ∀ p : A × B, op p p, by intro; apply and.intro; repeat {apply quasiorder.refl},
have trans : ∀ a b c, op a b → op b c → op a c, from λ x y z h1 h2, 
⟨(quasiorder.trans h1^.left h2^.left), quasiorder.trans h1^.right h2^.right⟩,
show _, from quasiorder.mk op refl trans

def terminal {A : Type} (o : A → A → Prop) (f : ℕ → A) (m : ℕ) := ∀ n, m < n → ¬ o (f m) (f n)

theorem lt_of_non_terminal {A : Type} {o : A → A → Prop} {f : ℕ → A} {m : ℕ} (H : ¬ @terminal _ o f m) : ∃ n, m < n ∧ o (f m) (f n) :=
let ⟨n,h⟩ := exists_not_of_not_forall H in ⟨n,(and_of_not_imp h)⟩

section
parameter {A : Type}
parameter [wqo A]
parameter f : ℕ → A

  section
  parameter H : ∀ N, ∃ r, N < r ∧ terminal wqo.le f r
  
  def terminal_index (n : ℕ) : {x : ℕ // n < x ∧ terminal wqo.le f x} := 
  nat.rec_on n (let i := some (H 0) in ⟨i, (some_spec (H 0))⟩)
  (λ pred index', 
   let i' := index'^.elt_of in
   let i := some (H i') in
   have p : i' < i ∧ terminal wqo.le f i, from some_spec (H i'),
   have pred < i', from (has_property index')^.left,
   have succ pred < i, from lt_of_le_of_lt this p^.left, 
   ⟨i, ⟨this,p^.right⟩⟩)

  lemma increasing_fti {n m : ℕ} : n < m → elt_of (terminal_index n) < elt_of (terminal_index m) :=
  nat.rec_on m (assume H, absurd H dec_trivial)
  (take a, assume IH, assume lt,
   have disj : n < a ∨ n = a, from lt_or_eq_of_lt_succ lt,
   have (terminal_index a)^.elt_of < (terminal_index (succ a))^.elt_of, from
     (some_spec $ H (terminal_index a)^.elt_of)^.left,
   or.elim disj (λ Hl, lt.trans (IH Hl) this) (λ Hr, by rw Hr;exact this))

  private def g (n : ℕ) := f (terminal_index n)^.elt_of

  lemma terminal_g (n : ℕ) : terminal wqo.le g n := 
  have ∀ n', (terminal_index n)^.elt_of < n' → ¬ wqo.le (f (terminal_index n)^.elt_of) (f n'), from 
    (has_property (terminal_index n))^.right,
  take n', assume h, this (terminal_index n')^.elt_of (increasing_fti h)

  lemma bad_g : ¬ is_good g wqo.le := 
  have H1 : ∀ i j, i < j → ¬ wqo.le (g i) (g j), from λ i, λ j, λ h, (terminal_g i) j h,
  suppose ∃ i j, i < j ∧ wqo.le (g i) (g j),
  let ⟨i,j,h⟩ := this in
  have ¬ wqo.le (g i) (g j), from H1 i j (and.left h),
  show _, from this (and.right h)

  lemma local_contradiction : false := bad_g (wqo.is_good g)

  end

theorem finite_terminal : ∃ N, ∀ r, N < r → ¬ terminal wqo.le f r := 
have ¬ ∀ N, ∃ r, N < r ∧ @terminal A wqo.le f r, by apply local_contradiction,
have ∃ N, ¬ ∃ r, N < r ∧ @terminal A wqo.le f r, by super,
let ⟨n,h⟩ := this in have ∀ r, n < r → ¬ @terminal A wqo.le f r, by super,
⟨n,this⟩

end

section

parameters {A B : Type}
parameter [wqo A]
parameter [wqo B]

  section

  parameter f : ℕ → A × B

  theorem  finite_terminal_on_A : ∃ N, ∀ r, N < r → ¬ @terminal A wqo.le (fst ∘ f) r := 
  finite_terminal (fst ∘ f)

  def sentinel := some finite_terminal_on_A

  def h_helper (n : ℕ) : {x : ℕ // sentinel < x ∧ ¬ @terminal A wqo.le (fst ∘ f) x} :=
  nat.rec_on n
  (have ∃ m, sentinel < m, by apply existence_of_nat_gt,
  let i := some this in have ge : sentinel < i, from some_spec this,
  have ¬ @terminal A wqo.le (fst ∘ f) i, from (some_spec finite_terminal_on_A) i ge,
  have sentinel < i ∧ ¬ terminal wqo.le (fst ∘ f) i, from ⟨ge,this⟩,
  ⟨i, this⟩)
  (λ pred h', let i' := elt_of h' in
  have lt' : sentinel < i', from (has_property h')^.left,
  have ¬ terminal wqo.le (fst ∘ f) i', from (has_property h')^.right,
  have ∃ n, i' < n ∧ ((fst ∘ f) i') ≤ ((fst ∘ f) n), from lt_of_non_terminal this,
  let i := some this in have i' < i, from (some_spec this)^.left,
  have lt : sentinel < i, from lt.trans lt' this,
  have ∀ r, sentinel < r → ¬ terminal wqo.le (fst ∘ f) r, from some_spec finite_terminal_on_A,
  have ¬ terminal wqo.le (fst ∘ f) i, from this i lt,
  have sentinel < i ∧ ¬ terminal wqo.le (fst ∘ f) i, from ⟨lt,this⟩,
  ⟨i,this⟩)

  private def h (n : ℕ) := (h_helper n)^.elt_of

  private lemma foo (a : ℕ) : h a < h (succ a) ∧ (fst ∘ f) (h a) ≤ (fst ∘ f) (h (succ a)) := 
  have ¬ terminal wqo.le (fst ∘ f) (h a), from (has_property $ h_helper a)^.right,
  have ∃ n, (h a) < n ∧ ((fst ∘ f) (h a)) ≤ ((fst ∘ f) n), from lt_of_non_terminal this,
  show _, from some_spec this

  theorem property_of_h {i j : ℕ} : i < j → (fst ∘ f) (h i) ≤ (fst ∘ f) (h j) :=
  nat.rec_on j (assume H, absurd H dec_trivial)
  (take a, assume IH, assume lt,
  have H1 : (fst ∘ f) (h a) ≤ (fst ∘ f) (h (succ a)), from (foo a)^.right,
  have disj : i < a ∨ i = a, from lt_or_eq_of_lt_succ lt,
  or.elim disj (λ Hl, wqo.trans (IH Hl) H1) (λ Hr, by simp [Hr, H1])) 

  theorem increasing_h {i j : ℕ} : i < j → h i < h j :=
  nat.rec_on j
  (assume H, absurd H dec_trivial)
  (take a, assume IH, assume lt,
  have H1 : (h a) < h (succ a), from (foo a)^.left,
  have disj : i < a ∨ i = a, from lt_or_eq_of_lt_succ lt,
  or.elim disj (λ Hl, lt.trans (IH Hl) H1) (λ Hr, by simp [Hr, H1]))

  theorem good_f : is_good f (o_for_pairs wqo.le wqo.le) :=
  have ∃ i j : ℕ, i < j ∧ (snd ∘ f ∘ h) i ≤ (snd ∘ f ∘ h) j, from wqo.is_good (snd ∘ f ∘ h),
  let ⟨i,j,H⟩ := this in
  have (fst ∘ f) (h i) ≤ (fst ∘ f) (h j), from property_of_h H^.left,
  have Hr : (fst ∘ f) (h i) ≤ (fst ∘ f) (h j) ∧ (snd ∘ f) (h i) ≤ (snd ∘ f) (h j), from and.intro this H^.right,
  have h i < h j, from increasing_h H^.left,
  ⟨(h i), (h j), ⟨this,Hr⟩⟩

  end
  
theorem good_pairs (f : ℕ → A × B) : is_good f (o_for_pairs wqo.le wqo.le) := good_f f

end

def wqo_prod {A B : Type} [HA : wqo A] [HB : wqo B] : wqo (A × B) :=
let op : A × B → A × B → Prop := o_for_pairs wqo.le wqo.le in
have refl : ∀ p : A × B, op p p, by intro; apply and.intro;repeat {apply wqo.refl},
have trans : ∀ a b c, op a b → op b c → op a c, from λ a b c h1 h2, 
  ⟨wqo.trans h1^.left h2^.left, wqo.trans h1^.right h2^.right⟩,
show _, from wqo.mk op refl trans good_pairs

-- example {A B : Type} [wqo A] [wqo B] : @wqo.le (A × B) (@wqo_prod A B _ _) = o_for_pairs wqo.le wqo.le := rfl

end kruskal
