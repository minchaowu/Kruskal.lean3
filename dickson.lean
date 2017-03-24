import data.set tools.super
open classical fin nat function prod subtype set super

noncomputable theory

theorem lt_or_eq_of_lt_succ {n m : ℕ} (H : n < succ m) : n < m ∨ n = m := 
lt_or_eq_of_le (le_of_lt_succ H)

theorem imp_of_not_and {p q : Prop} (H : ¬ (p ∧ q)) : p → ¬ q := by super
-- assume Hp Hq, H (and.intro Hp Hq)

theorem not_and_of_imp {p q : Prop} (H : p → ¬ q) : ¬ (p ∧ q) := by super
-- assume H1, have ¬ q, from H (and.left H1), this (and.right H1)

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

proposition le_refl {A : Type} [quasiorder A] (a : A) : a ≤ a := 
quasiorder.refl a

proposition le_trans {A : Type} [H : quasiorder A] {a b c : A} (H₁ : a ≤ b) (H₂ : b ≤ c) : a ≤ c := quasiorder.trans H₁ H₂
 
structure [class] wqo  (A : Type) extends quasiorder A : Type :=
(is_good : ∀ f : ℕ → A,  ∃ i j : ℕ, i < j ∧ le (f i) (f j))

definition is_good {A : Type} (f : ℕ → A) (o : A → A → Prop) := ∃ i j : ℕ, i < j ∧ o (f i) (f j)

definition o_for_pairs {A B : Type} (o₁ : A → A → Prop) (o₂ : B → B → Prop) (s : A × B) (t : A × B) := 
o₁ (s^.1) (t^.1) ∧ o₂ (s^.2) (t^.2) 

instance qo_prod  {A B: Type} [o₁ : quasiorder A] [o₂ : quasiorder B] : quasiorder (A × B) :=
let op : A × B → A × B → Prop  := o_for_pairs quasiorder.le quasiorder.le in
have refl : ∀ p : A × B, op p p, by intro; apply and.intro; repeat {apply quasiorder.refl},
have trans : ∀ a b c, op a b → op b c → op a c, from λ x y z h1 h2, 
⟨(quasiorder.trans h1^.left h2^.left), quasiorder.trans h1^.right h2^.right⟩,
show _, from quasiorder.mk op refl trans

definition terminal {A : Type} (o : A → A → Prop) (f : ℕ → A) (m : ℕ) := ∀ n, m < n → ¬ o (f m) (f n)

theorem prop_of_non_terminal {A : Type} {o : A → A → Prop} {f : ℕ → A} {m : ℕ} (H : ¬ @terminal _ o f m) : ∃ n, m < n ∧ o (f m) (f n) :=
let ⟨n,h⟩ := exists_not_of_not_forall H in ⟨n,(and_of_not_imp h)⟩

section
parameter {A : Type}
parameter [wqo A]
parameter f : ℕ → A

  section
  parameter H : ∀ N, ∃ r, N < r ∧ terminal wqo.le f r
  
  definition find_terminal_index (n : ℕ) : {x : ℕ // n < x ∧ terminal wqo.le f x} := 
  nat.rec_on n (let i := some (H 0) in tag i (some_spec (H 0)))
  (λ pred index', 
   let i' := (elt_of index') in
   let i := some (H i') in
   have p : i' < i ∧ terminal wqo.le f i, from some_spec (H i'),
   have lt : i' < i, from and.left p,
   have pred < i', from (has_property index')^.left,
   have succ pred ≤ i', from succ_le_of_lt this,
   have succ pred < i, from lt_of_le_of_lt this lt,
   have succ pred < i ∧ terminal wqo.le f i, from and.intro this (and.right p),
   tag i this)
  
  lemma increasing_fti {n m : ℕ} : n < m → elt_of (find_terminal_index n) < elt_of (find_terminal_index m) :=
  nat.induction_on m
  (assume H, absurd H dec_trivial)
  (take a, assume IH, assume lt,
   have disj : n < a ∨ n = a, from lt_or_eq_of_lt_succ lt,
   have elt_of (find_terminal_index a) < elt_of (find_terminal_index (succ a)), from (some_spec (H (elt_of (find_terminal_index a))))^.left,
   or.elim disj
   (λ Hl, lt.trans (IH Hl) this)
   (λ Hr, by rw Hr;exact this))

  private definition g (n : ℕ) := f (elt_of (find_terminal_index n))

  theorem terminal_g (n : ℕ) : terminal wqo.le g n := 
  have ∀ n', (elt_of (find_terminal_index n)) < n' → ¬ wqo.le (f (elt_of (find_terminal_index n))) (f n'), from and.right (has_property (find_terminal_index n)),
  take n', assume h, this (elt_of (find_terminal_index n')) (increasing_fti h)

  theorem bad_g : ¬ is_good g wqo.le := 
  have H1 : ∀ i j, i < j → ¬ wqo.le (g i) (g j), from λ i, λ j, λ h, (terminal_g i) j h,
  suppose ∃ i j, i < j ∧ wqo.le (g i) (g j),
  let ⟨i,j,h⟩ := this in
  have ¬ wqo.le (g i) (g j), from H1 i j (and.left h),
  show _, from this (and.right h)

  theorem local_contradiction : false := bad_g (wqo.is_good g)

  end

theorem finite_terminal : ∃ N, ∀ r, N < r → ¬ terminal wqo.le f r := 
have ¬ ∀ N, ∃ r, N < r ∧ @terminal A wqo.le f r, by apply local_contradiction,
have ∃ N, ¬ ∃ r, N < r ∧ @terminal A wqo.le f r, from exists_not_of_not_forall this,
let ⟨n,h⟩ := this in
have ∀ r, ¬ (n < r ∧ @terminal A wqo.le f r), by super,-- by rw forall_iff_not_exists at h;exact h,
have ∀ r, n < r → ¬ @terminal A wqo.le f r, from λ r, imp_of_not_and (this r),
show _, from exists.intro n this

end

section

parameters {A B : Type}
parameter [wqo A]
parameter [wqo B]

  section

  parameter f : ℕ → A × B

  theorem  finite_terminal_on_A : ∃ N, ∀ r, N < r → ¬ @terminal A wqo.le (fst ∘ f) r := 
  finite_terminal (fst ∘ f)

  definition sentinel := some finite_terminal_on_A

  definition h_helper (n : ℕ) : {x : ℕ // sentinel < x ∧ ¬ @terminal A wqo.le (fst ∘ f) x} :=
  nat.rec_on n
  (have ∃ m, sentinel < m, by apply existence_of_nat_gt,
  let i := some this in 
  have ge : sentinel < i, from some_spec this,
  have ¬ @terminal A wqo.le (fst ∘ f) i, from (some_spec finite_terminal_on_A) i ge,
  have sentinel < i ∧ ¬ terminal wqo.le (fst ∘ f) i, from  and.intro ge this,
  tag i this)
  (λ pred h', 
  let i' := elt_of h' in
  have lt' : sentinel < i', from (has_property h')^.left,
  have ¬ terminal wqo.le (fst ∘ f) i', from and.right (has_property h'),
  have ∃ n, i' < n ∧ ((fst ∘ f) i') ≤ ((fst ∘ f) n), from prop_of_non_terminal this,
  let i := some this in
  have i' < i, from (some_spec this)^.left,
  have lt : sentinel < i, from lt.trans lt' this,
  have ∀ r, sentinel < r → ¬ terminal wqo.le (fst ∘ f) r, from some_spec finite_terminal_on_A,
  have ¬ terminal wqo.le (fst ∘ f) i, from this i lt,
  have sentinel < i ∧ ¬ terminal wqo.le (fst ∘ f) i, from and.intro lt this,
  tag i this)

  private definition h (n : ℕ) := elt_of (h_helper n)

  private lemma foo (a : ℕ) : h a < h (succ a) ∧ (fst ∘ f) (h a) ≤ (fst ∘ f) (h (succ a)) := 
  have ¬ terminal wqo.le (fst ∘ f) (h a), from and.right (has_property (h_helper a)),
  have ∃ n, (h a) < n ∧ ((fst ∘ f) (h a)) ≤ ((fst ∘ f) n), from prop_of_non_terminal this,
  some_spec this

  theorem property_of_h {i j : ℕ} : i < j → (fst ∘ f) (h i) ≤ (fst ∘ f) (h j) :=
  nat.induction_on j
  (assume H, absurd H dec_trivial)
  (take a, assume IH, assume lt,
  have H1 : (fst ∘ f) (h a) ≤ (fst ∘ f) (h (succ a)), from (foo a)^.right,
  have disj : i < a ∨ i = a, from lt_or_eq_of_lt_succ lt,
  or.elim disj
  (λ Hl, wqo.trans (IH Hl) H1)
  (λ Hr, by simp [Hr, H1])) 

  theorem increasing_h {i j : ℕ} : i < j → h i < h j :=
  nat.induction_on j
  (assume H, absurd H dec_trivial)
  (take a, assume IH, assume lt,
  have H1 : (h a) < h (succ a), from and.left (foo a),
  have disj : i < a ∨ i = a, from lt_or_eq_of_lt_succ lt,
  or.elim disj
  (λ Hl, lt.trans (IH Hl) H1)
  (λ Hr, by simp [Hr, H1]))

  theorem good_f : is_good f (o_for_pairs wqo.le wqo.le) :=
  have ∃ i j : ℕ, i < j ∧ (snd ∘ f ∘ h) i ≤ (snd ∘ f ∘ h) j, from wqo.is_good (snd ∘ f ∘ h),
  let ⟨i,j,H⟩ := this in
  have (fst ∘ f) (h i) ≤ (fst ∘ f) (h j), from property_of_h (and.left H),
  have Hr : (fst ∘ f) (h i) ≤ (fst ∘ f) (h j) ∧ (snd ∘ f) (h i) ≤ (snd ∘ f) (h j), from and.intro this (and.right H),
  have h i < h j, from increasing_h (and.left H),
  have h i < h j ∧ (fst ∘ f) (h i) ≤ (fst ∘ f) (h j) ∧ (snd ∘ f) (h i) ≤ (snd ∘ f) (h j), from and.intro this Hr,
  ⟨(h i), (h j), this⟩

  end
  
theorem good_pairs : ∀ f : ℕ → A × B, is_good f (o_for_pairs wqo.le wqo.le) := good_f

end

instance wqo_prod  {A B : Type} [HA : wqo A] [HB : wqo B] : wqo (A × B) :=
let op : A × B → A × B → Prop := o_for_pairs wqo.le wqo.le in
have refl : ∀ p : A × B, op p p, by intro; apply and.intro;repeat {apply wqo.refl},
have trans : ∀ a b c, op a b → op b c → op a c,
  begin intros x y z h1 h2, apply and.intro,
  apply wqo.trans  (and.left h1) (and.left h2),
  apply wqo.trans (and.right h1) (and.right h2),
  end,
wqo.mk op refl trans good_pairs

end kruskal
