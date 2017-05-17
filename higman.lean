import .lemmas .dickson
open classical nat function prod set subtype

noncomputable theory

definition inj_from_to {A B: Type} (f : A → B) (S1 : set A) (S2 : set B) := maps_to f S1 S2 ∧ inj_on f S1

theorem inj_from_to_id {A : Type} (S1 : set A) : (∀ a, a ∈ S1 → id a ∈ S1) ∧ ∀ a₁ a₂, a₁ ∈ S1 → a₂ ∈ S1 → id a₁ = id a₂ → a₁ = a₂ := 
begin split, intros, simp, assumption, intros; assumption end

theorem inj_from_to_compose {A B C : Type} {g : B → C} {f : A → B} {S1 : set A} {S2 : set B} {S3 : set C} (Hg : inj_from_to g S2 S3) (Hf : inj_from_to f S1 S2) : inj_from_to (g ∘ f) S1 S3 :=
have Hl : ∀ a, a ∈ S1 → g (f a) ∈ S3, from 
  take a, assume Ha, have f a ∈ S2, from Hf^.left Ha,
  Hg^.left this,
have ∀ a₁ a₂, a₁ ∈ S1 → a₂ ∈ S1 → g (f a₁) = g (f a₂) → a₁ = a₂, from
  take a₁ a₂, assume Ha₁, assume Ha₂, assume Heq,
  have in1 : f a₁ ∈ S2, from and.left Hf Ha₁,
  have in2 : f a₂ ∈ S2, from and.left Hf Ha₂,
  have f a₁ = f a₂, from and.right Hg in1 in2 Heq, 
  and.right Hf Ha₁ Ha₂ this,
and.intro Hl this

theorem gt_of_gt_pred {a b : ℕ} (H : pred b < a) : b ≤ a :=
by_cases
(suppose b = 0, by simp [this,zero_le])
(suppose b ≠ 0, 
 have ∃ k, b = succ k, from exists_eq_succ_of_ne_zero this,
 let ⟨k,hk⟩ := this in
 have pred (succ k) < a, by rewrite hk at H;exact H,
 have k < a, by super, 
 have succ k ≤ a, from succ_le_of_lt this,
 by simp [this, hk])

theorem sub_gt_of_gt {a b c : ℕ} (H1 : a > b) (H2 : b > c) : a - c > b - c :=
have c ≤ a, from le_of_lt (gt.trans H1 H2),
have eq₁ : a - c + c = a, from nat.sub_add_cancel this,
have c ≤ b, from le_of_lt H2,
have eq₂ : b - c + c = b, from nat.sub_add_cancel this,
have b ≤ a, from le_of_lt H1,
have b - c ≤ a - c, from nat.sub_le_sub_right this c,
or.elim (nat.lt_or_eq_of_le this)
(assume Hl, Hl)
(assume Hr, have refl : a > a, by super,
 absurd refl (lt_irrefl a))

theorem lt_pred_nonzero_self {n : ℕ} (H : n ≠ 0) : pred n < n :=
have ∃ k, n = succ k, from exists_eq_succ_of_ne_zero H,
let ⟨k,hk⟩ := this in begin simp [hk, self_lt_succ] end

theorem eq_values_of_eq_func {A B : Type} {f g : A → B} (H : f = g) (a : A) : f a = g a := 
by rw H

theorem ne_empty_of_mem {X : Type} {s : set X} {x : X} (H : x ∈ s) : s ≠ ∅ := 
begin intro Hs, rewrite Hs at H, apply set.not_mem_empty _ H end 

theorem image_nonempty {A B : Type} {f : A → B} {S : set A} (H : S ≠ ∅) : image f  S ≠ ∅ :=
have ∃ s, s ∈ S, from exists_mem_of_ne_empty H,
let ⟨s,h⟩ := this in
have f s ∈ image f S, from exists.intro s (and.intro h rfl),
set.ne_empty_of_mem this

theorem not_mem_singleton {A : Type} (x a : A) (H : x ≠ a) : x ∉ insert a (∅ : set A) :=
suppose x ∈ insert a ∅, H (eq_of_mem_singleton this)

theorem refl_of_diff_of_ins_singleton {A : Type} {a : A} {S : set A} (H : a ∉ S) : S = (insert a S) \ insert a ∅ :=
subset.antisymm 
(λ x h, ⟨or.inr h,(λ neg, have x = a, from eq_of_mem_singleton neg,by super)⟩) 
(λ x ⟨hl,hr⟩, or.elim hl (λ l, 
have x ∈ insert a (∅ : set A), begin rw l, apply mem_singleton end, 
by contradiction) (λ r,r))

namespace kruskal

#check good_pairs

section
-- Given a countable set of objects A (which is ordered by f), and assuming that there exists a bad sequence (i.e., f ∘ g) of these objects, we can find a (sub)sequence (f ∘ h) which is bad and ∀ i, h 0 ≤ h i.
parameter {A : Type}
parameter f : ℕ → A
parameter g : ℕ → ℕ
parameter o : A → A → Prop
parameter H : ¬ is_good (f ∘ g) o

definition ran_g : set ℕ := {x : ℕ | ∃ i, g i = x}

theorem ne_empty_ran : ran_g ≠ ∅ := 
have g 0 ∈ ran_g, from exists.intro 0 rfl,
set.ne_empty_of_mem this

private definition min : ℕ := least ran_g ne_empty_ran

definition index_of_min : ℕ :=
have min ∈ ran_g, from least_is_mem ran_g ne_empty_ran,
some this 

theorem minimality_of_min (n : ℕ) : g index_of_min ≤ g n :=
have H1 : g index_of_min = min, from some_spec (least_is_mem ran_g ne_empty_ran),
have g n ∈ ran_g, from exists.intro n rfl,
have least ran_g ne_empty_ran ≤ g n, from minimality _ (g n) this,
begin simp [H1], exact this end

private definition h (n : ℕ) : ℕ := g (index_of_min + n)

theorem exists_sub_bad : ∃ h : ℕ → ℕ, ¬ is_good (f ∘ h) o ∧ ∀ i : ℕ, h 0 ≤ h i :=
have badness : ¬ is_good (f ∘ h) o, from
   suppose is_good (f ∘ h) o,
   let ⟨i,j,hij⟩ := this in
   have Hr : o (f (g (index_of_min + i))) (f (g (index_of_min + j))), from and.right hij,
   have index_of_min + i < index_of_min + j, from add_lt_add_left (and.left hij) _,
   have is_good (f ∘ g) o, from exists.intro (index_of_min + i) (exists.intro (index_of_min + j) (and.intro this Hr)),
   H this,
have ∀ i : ℕ, h 0 ≤ h i, from λ i, minimality_of_min (index_of_min + i),
⟨h,⟨badness,this⟩⟩

end

definition finite_subsets (Q : Type) : Type := {x : set Q // finite x}

definition non_descending {Q : Type} (A B : finite_subsets Q) (o : Q → Q → Prop) (f : Q → Q) := ∀ a : Q, a ∈ A.1 → o a (f a) ∧ f a ∈ B.1

definition order_on_finite_subsets {Q : Type} (o : Q → Q → Prop) (A B : finite_subsets Q) := ∃ f, inj_from_to f A.1 B.1 ∧ non_descending A B o f

definition extends_at {A : Type} (n : ℕ) (f : ℕ → A) (g : ℕ → A) : Prop := ∀ m, m ≤ n → g m = f m

theorem extends_at.refl {A : Type} {n : ℕ} {f : ℕ → A} : extends_at n f f := λ m H, rfl

theorem extends_at.trans {A : Type} {n m : ℕ} {f g h: ℕ → A} (H1 : extends_at n f g) (H2 : extends_at m g h) (H3 : n ≤ m) : extends_at n f h :=
take k, assume H,
have g k = f k, from H1 k H,
have k ≤ m, from nat.le_trans H H3,
have h k = g k, from H2 k this,
by super

definition induced_set_of_exists {A : Type} {P : A → Prop} (H : ∃ x, P x) : set A := {x | P x}

theorem nonempty_induced_set {A : Type} {P : A → Prop} (H : ∃ x, P x) : induced_set_of_exists H ≠ ∅ := let ⟨a,h⟩ := H in set.ne_empty_of_mem h

theorem property_of_induced_set {A : Type} {P : A → Prop} (H : ∃ x, P x) : ∀ s, s ∈ induced_set_of_exists H → P s := 
λ s h, h

theorem least_seq_at_n {S : set (ℕ → ℕ)} (H : S ≠ ∅) (n : ℕ) : ∃ f, f ∈ S ∧ ∀ g, g ∈ S → f n ≤ g n :=
let T : set ℕ := {x | ∃ f, f ∈ S ∧ f n = x} in
have ∃ f, f ∈ S, from exists_mem_of_ne_empty H,
let ⟨f,h⟩ := this in
have f n ∈ T, from exists.intro f (and.intro h rfl),
have nemp : T ≠ ∅, from set.ne_empty_of_mem this,
let a := least T nemp in
have a ∈ T, from least_is_mem T nemp,
let ⟨f',h⟩ := this in
have f' n = a, from and.right h,
have ∀ g, g ∈ S → f' n ≤ g n, from
  take g, assume Hg, have g n ∈ T, from exists.intro g (and.intro Hg rfl),
  have a ≤ g n, from minimality _ _ this, 
  by super,
exists.intro f' (and.intro (and.left h) this)


section
-- given an n, take an f from {f | P f} such that |f n| is as small as possible.
parameter {A : Type}
parameter {P : (ℕ → A) → Prop}
parameter g : A → ℕ -- a function which calculates the cardinality of a : A in some sense.
parameter H : ∃ f : ℕ → A, P f

definition card_of_f (f : ℕ → A) (n : ℕ) := g (f n)

definition set_of_f := induced_set_of_exists H

lemma nonempty_set_of_f : set_of_f ≠ ∅ :=  nonempty_induced_set H

definition S : set (ℕ → ℕ) := image card_of_f set_of_f

lemma nonempty_S : S ≠ ∅ := image_nonempty nonempty_set_of_f

theorem exists_min_f (n : ℕ) : ∃ f, f ∈ S ∧ ∀ g, g ∈ S → f n ≤ g n := least_seq_at_n nonempty_S n

-- let ⟨l,r⟩ := some_spec (exists_min_f n) does not work
definition minf_at_n (n : ℕ) : ℕ → A := 
let fc := some (exists_min_f n) in
have fc ∈ S ∧ ∀ g, g ∈ S → fc n ≤ g n, from (some_spec (exists_min_f n)),
some (and.left this)

theorem property_of_minf (n : ℕ) : P (minf_at_n n) :=
let fc := some (exists_min_f n) in
let ⟨l,r⟩ := some_spec (exists_min_f n) in
-- have fc ∈ S, from sorry,--and.left (some_spec (exists_min_f n)),
have minf_at_n n = some l, from rfl,
have minf_at_n n ∈ set_of_f ∧ card_of_f (minf_at_n n) = fc, from some_spec l ,
have minf_at_n n ∈ set_of_f, from and.left this,
property_of_induced_set  _  _ this

-- For every f satisfying P, we have the inequality. Intuitively, it says that |(minf_at_n n) n| is always less than or equal to |f n|.
theorem minimality_of_minf (f : ℕ → A) (Hp : P f) (n : ℕ) : g (minf_at_n n n) ≤ g (f n) := 
let fc := some (exists_min_f n) in
let ⟨l,r⟩ := some_spec (exists_min_f n) in
-- have fc ∈ S, from and.left (some_spec (exists_min_f n)),
have minf_at_n n ∈ set_of_f ∧ card_of_f (minf_at_n n) = fc, from some_spec l,
have card_of_f (minf_at_n n) = fc, from and.right this, 
have eq2 : card_of_f (minf_at_n n) n = fc n, from eq_values_of_eq_func this n, 
have Hr : ∀ g, g ∈ S → fc n ≤ g n, from and.right (some_spec (exists_min_f n)),
have card_of_f f ∈ S, from exists.intro f (and.intro Hp rfl),
have le : fc n ≤ card_of_f f n, from Hr _ this,
have card_of_f (minf_at_n n) n = g (minf_at_n n n), from rfl,
have card_of_f f n = g (f n), from rfl,
have card_of_f (minf_at_n n) n ≤ card_of_f f n, by rewrite -eq2 at le;exact le,
by super

end

section

parameter {A : Type} 
parameter {P : (ℕ → A) → Prop} -- some property about f 
parameter g : A → ℕ -- a measure of cardinality of A 
parameter H : ∃ f, P f 

-- construct a sequence of functions with property P such that each one extends its predecessor and is the minimal one at n.
noncomputable definition mbs_helper (n : ℕ) : {f : ℕ → A // P f} :=
nat.rec_on n
(let f₀ := minf_at_n g H 0 in
 have P f₀, from property_of_minf g H 0,
 ⟨f₀,this⟩)
(λ pred h',
let f' := h'.1 in
have H1 : extends_at pred f' f', from extends_at.refl,
have H2 : P f', from h'.2,
have HP : ∃ f, extends_at pred f' f ∧ P f, from exists.intro f' (and.intro H1 H2),
let fn := minf_at_n g HP (succ pred) in
have extends_at pred f' fn ∧ P fn, from property_of_minf g HP (succ pred),
have P fn, from and.right this,
⟨fn,this⟩)

  section
  parameter n : ℕ
  definition helper_elt := (mbs_helper n).1
  definition helper_succ := (mbs_helper (succ n)).1
  lemma helper_ext_refl : extends_at n helper_elt helper_elt := extends_at.refl
  lemma helper_has_property : P helper_elt := (mbs_helper n).2
  lemma helper_inner_hyp : ∃ g, extends_at n helper_elt g ∧ P g := exists.intro helper_elt (and.intro helper_ext_refl helper_has_property)
  theorem succ_ext_of_mbs_helper : extends_at n helper_elt helper_succ := and.left (property_of_minf g helper_inner_hyp (succ n))
  end

theorem ext_of_mbs_helper (n : ℕ) : ∀ m, m ≤ n → extends_at m  (mbs_helper m).1 (mbs_helper n).1 :=
nat.rec_on n
(take m, assume H, 
have eq : m = 0, from eq_zero_of_le_zero H,
have extends_at 0 (mbs_helper 0).1 (mbs_helper 0).1, from extends_at.refl,
by simp [eq,this])
(take a, assume IH, 
take m, assume H,
by_cases
(suppose m = succ a, 
have extends_at m (mbs_helper (succ a)).1 (mbs_helper (succ a)).1, from extends_at.refl, by super)
(suppose m ≠ succ a, 
have m < succ a, from lt_of_le_of_ne H this,
have Hle : m ≤ a, from (iff.mp (lt_succ_iff_le m a)) this,
have H1 : extends_at m (mbs_helper m).1 (mbs_helper a).1, from IH m Hle,
have extends_at a (mbs_helper a).1 (mbs_helper (succ a)).1, from succ_ext_of_mbs_helper a,
extends_at.trans H1 this Hle))

theorem congruence_of_mbs_helper {n m : ℕ} (H : m ≤ n) : (mbs_helper n).1 m = (mbs_helper m).1 m :=
have extends_at m (mbs_helper m).1 (mbs_helper n).1, from ext_of_mbs_helper n m H,
this m (nat.le_refl m)

end

section
-- construction and properties of mbs.
parameter {A : Type}
parameter {o : A → A → Prop}
parameter g : A → ℕ
parameter H : ∃ f : ℕ → A, ¬ is_good f o

noncomputable definition seq_of_bad_seq (n : ℕ) : {f : ℕ → A // ¬ is_good f o} := mbs_helper g H n

definition minimal_bad_seq (n : ℕ) : A :=  (seq_of_bad_seq n).1 n 

definition ext_of_seq_of_bad_seq := ext_of_mbs_helper g H

definition congruence_of_seq_of_bad_seq {n m : ℕ} (Hnm : m ≤ n) := congruence_of_mbs_helper g H Hnm

definition bad_seq_elt := helper_elt g H

definition bad_seq_inner_hyp := helper_inner_hyp g H 

theorem badness_of_mbs : ¬ is_good minimal_bad_seq o := 
suppose is_good minimal_bad_seq o,
let ⟨i,j,h⟩ := this in
have le : i < j, from and.left h,
have i ≤ j, from le_of_lt_or_eq (or.intro_left (i = j) le),
have ext : extends_at i (seq_of_bad_seq i).1 (seq_of_bad_seq j).1, from ext_of_seq_of_bad_seq j i this,
have i ≤ i, from nat.le_refl i,
have (seq_of_bad_seq j).1 i = (minimal_bad_seq i), from ext i this,
have o ((seq_of_bad_seq j).1 i) (minimal_bad_seq j), by rw this; exact h^.right,
have i < j ∧ o ((seq_of_bad_seq j).1 i) ((seq_of_bad_seq j).1 j), from and.intro le this,
have good : is_good (seq_of_bad_seq j).1 o, from exists.intro i (exists.intro j this),
have ¬ is_good (seq_of_bad_seq j).1 o, from (seq_of_bad_seq j).2, 
this good

theorem minimality_of_mbs_0 (f : ℕ → A) (Hf : ¬ is_good f o) : g (minimal_bad_seq 0) ≤ g (f 0) := minimality_of_minf g H f Hf 0

theorem minimality_of_mbs (n : ℕ) (f : ℕ → A) (H1 : extends_at n minimal_bad_seq f ∧ ¬ is_good f o) : g (minimal_bad_seq (succ n)) ≤ g (f (succ n)) := 
have Hl : ∀ m, m ≤ n →  f m = (bad_seq_elt n) m, from 
  take m, assume Hle, have f m = minimal_bad_seq m, from and.left H1 m Hle,
  have bad_seq_elt n m = minimal_bad_seq m, from congruence_of_seq_of_bad_seq Hle,
  by super, --by+ simp,
have ins_P : extends_at n (bad_seq_elt n) f ∧ ¬ is_good f o, from and.intro Hl (and.right H1),
have ineq : g (minf_at_n g (bad_seq_inner_hyp n) (succ n) (succ n)) ≤ g (f (succ n)), from minimality_of_minf g (bad_seq_inner_hyp n) f ins_P (succ n), 
have minimal_bad_seq (succ n) = minf_at_n g (bad_seq_inner_hyp n) (succ n) (succ n), from rfl,
-- by+ rewrite (eq.symm this) at ineq; exact ineq
by super

end

section

-- Given two sequences f and g, a function h which modifies indices so that h 0 is the break point, construct a new sequence 'combined_seq' by concatenating f and g at (h 0).

parameter {Q :Type}
parameter {o : Q → Q → Prop}
parameters f g : ℕ → Q
parameter h : ℕ → ℕ
parameter Hh : ∀ i, h 0 ≤ h i
parameter Hf : ¬ is_good f o
parameter Hg : ¬ is_good g o
-- in Higman's lemma in Williams 1963, h is f, g is the bad sequence B ∘ f
parameter H : ∀ i j, o (f i) (g (j - h 0)) → o (f i) (f (h (j - h 0))) 

definition combined_seq (n : ℕ) : Q := if h 0 ≠ 0 ∧ n ≤ pred (h 0) then f n else g (n - (h 0))

theorem g_part_of_combined_seq (H : (h 0) = 0) : ∀ x, combined_seq x = g x :=
take n, have ¬ (h 0) ≠ 0, from not_not_intro H,
have ¬ ((h 0) ≠ 0 ∧ n ≤ pred (h 0)), from not_and_of_not_left (n ≤ pred (h 0)) this,
have combined_seq n = g (n - (h 0)), from if_neg this,
by simp [this, H]

theorem badness_of_combined_seq : ¬ is_good combined_seq o := 
λ good, 
let ⟨i,j,hw⟩ := good in
by_cases
(suppose (h 0) = 0, 
have combined_seq = g, begin apply funext, apply g_part_of_combined_seq, exact this end,
have is_good g o, by rw this at good;exact good,
Hg this)
(assume ne, 
  by_cases
  (assume Hposi : i ≤ pred (h 0), 
   have eq1i : combined_seq i = f i, from if_pos (and.intro ne Hposi),
   by_cases
     (suppose j ≤ pred (h 0), 
      have eq1j : combined_seq j = f j, from if_pos (and.intro ne this), 
      have o (combined_seq i) (combined_seq j), from and.right hw,
      have o (combined_seq i) (f j), by rewrite eq1j at this; exact this,
      have o (f i) (f j), begin rw -eq1i, exact this end,
      have is_good f o, from exists.intro i (exists.intro j (and.intro (and.left hw) this)),
      show _, from Hf this)
     (suppose ¬ j ≤ pred (h 0), 
      have ¬ ((h 0) ≠ 0 ∧ j ≤ pred (h 0)), from not_and_of_not_right ((h 0) ≠ 0) this,
      have eq2j : combined_seq j = g (j - (h 0)), from if_neg this, 
      have o (f i) (g (j - (h 0))), begin rw [-eq2j,-eq1i], exact hw^.right end,
     have Hr : o (f i) (f (h (j - (h 0)))), from H _ _ this,
     have i < h (j - (h 0)), from
       have ilth0 : i < h 0, from lt_of_le_of_lt Hposi (lt_pred_nonzero_self ne),
       have h 0 ≤ h (j - h 0), from Hh (j - h 0), 
       show _, from lt_of_lt_of_le ilth0 this,
     have is_good f o, from exists.intro i (exists.intro (h (j - h 0)) (and.intro this Hr)),
     show _, from Hf this))
  (assume Hnegi, 
   have iht : pred (h 0) < i, from lt_of_not_ge Hnegi,
   have ¬ (h 0 ≠ 0 ∧ i ≤ pred (h 0)), from not_and_of_not_right (h 0 ≠ 0) Hnegi,
   have eq2i : combined_seq i = g (i - h 0), from if_neg this,
   by_cases
   (assume Hposj : j ≤ pred (h 0), 
    have j < i, from lt_of_le_of_lt Hposj iht,
    show _, from (not_lt_of_gt (and.left hw)) this)
   (assume Hnegj, 
    have pred (h 0) < j, from lt_of_not_ge Hnegj,
    have ¬ (h 0 ≠ 0 ∧ j ≤ pred (h 0)), from not_and_of_not_right (h 0 ≠ 0) Hnegj,
    have eq2j : combined_seq j = g (j - h 0), from if_neg this,
    have o (combined_seq i) (combined_seq j), from and.right hw,
    have o (combined_seq i) (g (j - h 0)), begin rw -eq2j, exact this end, --by simp,
    have Hr2 : o (g (i - h 0)) (g (j - h 0)), begin rw -eq2i, exact this end,-- by simp,
    have ige : h 0 ≤ i, from gt_of_gt_pred iht,
    have jgt : h 0 < j, from lt_of_le_of_lt ige (and.left hw),
    have i - h 0 < j - h 0, from 
     or.elim (lt_or_eq_of_le ige)
     (assume hl, sub_gt_of_gt (and.left hw) hl)
     (assume hr, have 0 < j - h 0, from nat.sub_pos_of_lt jgt, 
      have i - h 0 = 0, begin rw hr, apply nat.sub_self end,
      begin rw this, assumption end),
      have is_good g o, from exists.intro (i - h 0) (exists.intro (j - h 0) (and.intro this Hr2)),
     show _, from Hg this)))

-- assume good : is_good combined_seq o,
-- let ⟨i,j,hw⟩ := good in
-- --obtain (i j) hw, from good,
-- by_cases
-- (suppose (h 0) = 0,
--  have combined_seq = g, from funext (g_part_of_combined_seq this),
--  have is_good g o, from sorry,-- by rewrite this at good;exact good,
--  Hg this)
-- (assume ne, 
--   by_cases
--   (assume Hposi : i ≤ pred (h 0), 
--    have eq1i : combined_seq i = f i, from if_pos (and.intro ne Hposi),
--    by_cases
--    (suppose j ≤ pred (h 0), 
--     have eq1j : combined_seq j = f j, from if_pos (and.intro ne this), 
--     have o (combined_seq i) (combined_seq j), from and.right hw,
--     have o (combined_seq i) (f j), from sorry,-- by rewrite eq1j at this; exact this,
--     have o (f i) (f j), from sorry,--by simp,
--     have is_good f o, from exists.intro i (exists.intro j (and.intro (and.left hw) this)),
--     Hf this)
--    (suppose ¬ j ≤ pred (h 0), 
--     have ¬ ((h 0) ≠ 0 ∧ j ≤ pred (h 0)), from not_and_of_not_right ((h 0) ≠ 0) this,
--     have eq2j : combined_seq j = g (j - (h 0)), from if_neg this, 
--     have o (f i) (g (j - (h 0))), from sorry, --by simp,
--     have Hr : o (f i) (f (h (j - (h 0)))), from sorry, --H this,
--     have i < h (j - (h 0)), from
--       have ilth0 : i < h 0, from lt_of_le_of_lt Hposi (lt_pred_nonzero_self ne),
--       have h 0 ≤ h (j - h 0), from Hh (j - h 0),
--       lt_of_lt_of_le ilth0 this,
--     have is_good f o, from exists.intro i (exists.intro (h (j - h 0)) (and.intro this Hr)),
--     Hf this))
--   (assume Hnegi : ¬ i ≤ pred (h 0), 
--    have iht : pred (h 0) < i, from lt_of_not_ge Hnegi,
--    have ¬ (h 0 ≠ 0 ∧ i ≤ pred (h 0)), from not_and_of_not_right (h 0 ≠ 0) Hnegi,
--    have eq2i : combined_seq i = g (i - h 0), from if_neg this,
--    by_cases
--    (assume Hposj : j ≤ pred (h 0), 
--     have j < i, from lt_of_le_of_lt Hposj iht,
--     (not_lt_of_gt (and.left hw)) this)
--     (assume Hnegj : ¬ j ≤ pred (h 0), 
--      have pred (h 0) < j, from lt_of_not_ge Hnegj,
--      have ¬ (h 0 ≠ 0 ∧ j ≤ pred (h 0)), from not_and_of_not_right (h 0 ≠ 0) Hnegj,
--      have eq2j : combined_seq j = g (j - h 0), from if_neg this,
--      have o (combined_seq i) (combined_seq j), from and.right hw,
--      have o (combined_seq i) (g (j - h 0)), from sorry, --by simp,
--      have Hr2 : o (g (i - h 0)) (g (j - h 0)), from sorry,-- by simp,
--      have ige : h 0 ≤ i, from gt_of_gt_pred iht,
--      have jgt : h 0 < j, from lt_of_le_of_lt ige (and.left hw),
--      have i - h 0 < j - h 0, from 
--      or.elim (lt_or_eq_of_le ige)
--      (assume hl, sub_gt_of_gt (and.left hw) hl)
--      (assume hr, have 0 < j - h 0, from nat.sub_pos_of_lt jgt, sorry--by simp
-- ),
--      have is_good g o, from exists.intro (i - h 0) (exists.intro (j - h 0) (and.intro this Hr2)),
--      Hg this)))

end

-- section
-- -- further assume that f is a minimal bad sequence and card (g 0) < card (f (h 0)) 
-- -- In other words, this section says, assuming that there is a bad sequence of Q, if g is a bad sequence such that H holds, then there is a contradiction. 
-- parameter {Q :Type}
-- parameter {o : Q → Q → Prop}
-- parameters {g : ℕ → Q}
-- parameter h : ℕ → ℕ
-- parameter m : Q → ℕ -- a measure of cardinality
-- parameter Hh : ∀ i, h 0 ≤ h i
-- parameter Hex : ∃ f, ¬ is_good f o
-- parameter Hg : ¬ is_good g o
-- parameter H : ∀ i j, o (minimal_bad_seq m Hex i) (g (j - h 0)) → o (minimal_bad_seq m Hex i) ((minimal_bad_seq m Hex) (h (j - h 0)))
-- parameter Hbp : m (g 0) < m (minimal_bad_seq m Hex (h 0))

-- definition comb_seq_with_mbs := combined_seq (minimal_bad_seq m Hex) g h

-- theorem g_part_of_comb_seq_with_mbs (H1 : (h 0) = 0) : ∀ x, comb_seq_with_mbs x = g x := 
-- g_part_of_combined_seq (minimal_bad_seq m Hex) g h H1

-- theorem badness_of_comb_seq_with_mbs : ¬ is_good comb_seq_with_mbs o := 
-- badness_of_combined_seq (minimal_bad_seq m Hex) g h Hh (badness_of_mbs m Hex) Hg H

-- theorem comb_seq_extends_mbs_at_pred_bp (H : h 0 ≠ 0): extends_at (pred (h 0)) (minimal_bad_seq m Hex) comb_seq_with_mbs := λ m, λ Hm, if_pos (and.intro H Hm)

-- lemma comb_seq_h0 : comb_seq_with_mbs (h 0) = g 0 := 
-- by_cases
-- (suppose h 0 = 0, 
-- have comb_seq_with_mbs (h 0) = g (h 0), from g_part_of_comb_seq_with_mbs this (h 0),
-- by+ simp)
-- (suppose h 0 ≠ 0, 
-- have pred (h 0) < h 0, from lt_pred_nonzero_self this,
-- have ¬ h 0 ≤ pred (h 0), from not_le_of_gt this,
-- have ¬ ((h 0) ≠ 0 ∧ h 0 ≤ pred (h 0)), from not_and_of_not_right ((h 0) ≠ 0) this,
-- have comb_seq_with_mbs (h 0) = g (h 0 - h 0), from if_neg this,
-- by+ simp)

-- theorem local_contra_of_comb_seq_with_mbs : false := 
-- by_cases
-- (suppose h 0 = 0, 
-- have eq : comb_seq_with_mbs 0 = g 0, from g_part_of_comb_seq_with_mbs this 0,
-- have m (comb_seq_with_mbs 0) < m (minimal_bad_seq m Hex (h 0)), by+ rewrite -eq at Hbp;exact Hbp,
-- have le : m (comb_seq_with_mbs 0) < m (minimal_bad_seq m Hex 0), by+ simp,
-- have m (minimal_bad_seq m Hex 0) ≤ m (comb_seq_with_mbs 0), from minimality_of_mbs_0 m Hex comb_seq_with_mbs badness_of_comb_seq_with_mbs,
-- (not_le_of_gt le) this)
-- (assume Hneg, 
-- have le : m (minimal_bad_seq m Hex (succ (pred (h 0)))) ≤  m (comb_seq_with_mbs (succ (pred (h 0)))), from minimality_of_mbs m Hex (pred (h 0)) comb_seq_with_mbs (and.intro (comb_seq_extends_mbs_at_pred_bp Hneg) badness_of_comb_seq_with_mbs),
-- have h 0 > 0, from pos_of_ne_zero Hneg,
-- have succ (pred (h 0)) = h 0, from succ_pred_of_pos this,
-- have m (minimal_bad_seq m Hex (h 0)) ≤ m (comb_seq_with_mbs (h 0)), by+ rewrite this at le;exact le,
-- have m (minimal_bad_seq m Hex (h 0)) ≤ m (g 0), by+ rewrite comb_seq_h0 at this;exact this,
-- have ¬ m (g 0) < m (minimal_bad_seq m Hex (h 0)), from not_lt_of_ge this, 
-- this Hbp)

-- end

-- check local_contra_of_comb_seq_with_mbs

-- section
-- parameter {Q : Type}
-- parameter [wqo Q]

-- definition ofs := @order_on_finite_subsets Q wqo.le

-- theorem ofs_refl (q : finite_subsets Q) : ofs q q :=
-- have ∀ a : Q, a ∈ elt_of q → wqo.le a (id a) ∧ id a ∈ elt_of q, by intros;split;apply wqo.refl;simp,
-- exists.intro id (and.intro (inj_from_to_id (elt_of q)) this)

-- theorem ofs_trans (a b c : finite_subsets Q) (H1 : ofs a b) (H2 : ofs b c) : ofs a c :=
-- obtain f hf, from H1,
-- obtain g hg, from H2,
-- have inj : inj_from_to (g ∘ f) (elt_of a) (elt_of c), from inj_from_to_compose (and.left hg) (and.left hf),
-- have ∀ q : Q, q ∈ elt_of a → wqo.le q ((g ∘ f) q) ∧ (g ∘ f) q ∈ elt_of c, from 
--   take q, assume Hq,
--   have le1 : wqo.le q (f q), from and.left ((and.right hf) q Hq),
--   have fqin : f q ∈ elt_of b, from and.right ((and.right hf) q Hq),
--   have le2 : wqo.le (f q) ((g ∘ f) q), from and.left ((and.right hg) (f q) fqin),
--   have qle : wqo.le q ((g ∘ f) q), from !wqo.trans le1 le2,
--   have (g ∘ f) q ∈ elt_of c, from and.right ((and.right hg) (f q) fqin),
--   and.intro qle this,
-- exists.intro (g ∘ f) (and.intro inj this)

-- parameter H : ∃ f : ℕ → finite_subsets Q, ¬ is_good f ofs

-- definition card_of_finite_subsets {A : Type} (s : finite_subsets A) := card (elt_of s)

-- definition Higman's_mbs (n : ℕ) : finite_subsets Q := minimal_bad_seq card_of_finite_subsets H n

-- theorem badness_of_Higman's_mbs : ¬ is_good Higman's_mbs ofs := badness_of_mbs card_of_finite_subsets H

-- theorem nonempty_mem_of_mbs (n : ℕ) : elt_of (Higman's_mbs n) ≠ ∅ := 
-- suppose elt_of (Higman's_mbs n) = ∅, 
-- have lt : n < succ n, from lt_succ_self n,
-- have nondescending : ∀ a : Q, a ∈ elt_of (Higman's_mbs n) → wqo.le a (id a) ∧ id a ∈ elt_of (Higman's_mbs (succ n)), from 
--   λ a, λ H, have a ∉ ∅, from not_mem_empty a, by+ simp,
-- have ofs (Higman's_mbs n) (Higman's_mbs (succ n)), 
-- begin+ fapply exists.intro,exact id,repeat split,
--   intros a Ha,apply and.right (nondescending a Ha),
--   intros,simp,apply nondescending end,
-- have is_good Higman's_mbs ofs, from exists.intro n (exists.intro (succ n) (and.intro lt this)),
-- badness_of_Higman's_mbs this

-- definition B_pairs (n : ℕ) : Q × finite_subsets Q := 
-- have ∃ a : Q, a ∈ elt_of (Higman's_mbs n), from exists_mem_of_ne_empty (nonempty_mem_of_mbs n),
-- let q := some this in
-- let b := elt_of (Higman's_mbs n) \ '{q} in
-- have finite (elt_of (Higman's_mbs n)), from has_property (Higman's_mbs n),
-- have finite b, from proof @finite_diff _ _ _ this qed,
-- (q, tag b this)

-- private definition B (n : ℕ) : finite_subsets Q := pr2 (B_pairs n)

-- definition qn (n : ℕ) : Q := pr1 (B_pairs n)

-- theorem qn_in_mbs (n : ℕ) : qn n ∈ elt_of (Higman's_mbs n) :=
-- some_spec (exists_mem_of_ne_empty (nonempty_mem_of_mbs n))

-- theorem qn_not_in_Bn (n : ℕ) : qn n ∉ elt_of (B n) := 
-- suppose qn n ∈ elt_of (B n), (and.right this) (mem_singleton (qn n))

-- theorem ins_B_pairs (n : ℕ) : insert (qn n) (elt_of (B n)) = elt_of (Higman's_mbs n) :=
-- have ∃ a : Q, a ∈ elt_of (Higman's_mbs n), from exists_mem_of_ne_empty (nonempty_mem_of_mbs n),
-- have qnin : qn n ∈ elt_of (Higman's_mbs n), from some_spec this,
-- have elt_of (B n) = elt_of (Higman's_mbs n) \ '{qn n}, from rfl,
-- begin+ apply subset.antisymm, intros x H1, apply or.elim H1, 
--   intro, simp, intro, have x ∈ elt_of (Higman's_mbs n) \ '{qn n}, by simp, 
--   apply and.left this,
--   intros x H2, cases (decidable.em (x = qn n)) with [H3, H4],
--   apply or.inl, exact H3,
--   apply or.inr, rewrite this, apply and.intro, exact H2,
--   apply not_mem_singleton, exact H4 end

-- theorem sub_B_mbs (n : ℕ) : elt_of (B n) ⊆ elt_of (Higman's_mbs n) :=
-- by intros; intro; rewrite -ins_B_pairs; apply or.inr; assumption

-- theorem trans_of_B (i j : ℕ) (H1 : ofs (Higman's_mbs i) (B j)) : ofs (Higman's_mbs i) (Higman's_mbs j) :=
-- obtain f hf, from H1,
-- have inj_from_to f (elt_of (Higman's_mbs i)) (elt_of (B j)), from and.left hf,
-- have Hl : ∀ a, a ∈ elt_of (Higman's_mbs i) → f a ∈ elt_of (Higman's_mbs j), from
--   take a, assume Ha, have f a ∈ elt_of (B j), from and.left this a Ha, 
--   (sub_B_mbs j) this,
-- have inj : inj_from_to f (elt_of (Higman's_mbs i)) (elt_of (Higman's_mbs j)), from and.intro Hl (and.right (and.left hf)),
-- have non_descending (Higman's_mbs i) (Higman's_mbs j) wqo.le f, from 
--   take a, assume Ha, have Hl : wqo.le a (f a), from and.left ((and.right hf) a Ha),
--   have f a ∈ elt_of (B j), from and.right ((and.right hf) a Ha),
--   have fain : f a ∈ insert (qn j) (elt_of (B j)), from or.intro_right (f a = qn j) this,
--   have insert (qn j) (elt_of (B j)) = elt_of (Higman's_mbs j), from ins_B_pairs j,
--   have f a ∈ elt_of (Higman's_mbs j), by+ rewrite this at fain;exact fain,
--   and.intro Hl this,
-- exists.intro f (and.intro inj this)

-- section
-- parameter Hg : ∃ g : ℕ → ℕ, ¬ is_good (B ∘ g) ofs ∧ ∀ i : ℕ, g 0 ≤ g i

-- private definition g := some Hg

-- theorem Higman's_Hg : ¬ is_good (B ∘ g) ofs := and.left (some_spec Hg)

-- theorem Higman's_Hex : ∃ f, ¬ is_good f ofs := exists.intro (B ∘ g) Higman's_Hg

-- theorem Higman's_Hh : ∀ i : ℕ, g 0 ≤ g i := and.right (some_spec Hg)

-- theorem Higman's_H : ∀ i j, ofs (Higman's_mbs i) ((B ∘ g) (j - g 0)) → ofs (Higman's_mbs i) (Higman's_mbs (g (j - g 0))) := λ i j, λ H1, trans_of_B i (g (j - g 0)) H1

-- definition Higman's_comb_seq (n : ℕ) : finite_subsets Q := @comb_seq_with_mbs _ ofs (B ∘ g) g card_of_finite_subsets Higman's_Hex n

-- theorem card_B_lt_mbs (n : ℕ) : card (elt_of (B n)) < card (elt_of (Higman's_mbs n)) :=
-- have finite (elt_of (B n)), from has_property (B n),
-- have card (insert (qn n) (elt_of (B n))) = card (elt_of (B n)) + 1, from @card_insert_of_not_mem _ _ _ this (qn_not_in_Bn n), 
-- have card (elt_of (B n)) < card (elt_of (B n)) + 1, from lt_succ_self (card (elt_of (B n))), 
-- have card (elt_of (B n)) < card (insert (qn n) (elt_of (B n))), by+ simp,
-- have insert (qn n) (elt_of (B n)) = elt_of (Higman's_mbs n), from ins_B_pairs n,
-- by+ simp

-- theorem Higman's_Hbp : card_of_finite_subsets (B (g 0)) < card_of_finite_subsets (Higman's_mbs (g 0)) := card_B_lt_mbs (g 0)

-- theorem Higman's_local_contradition : false := 
-- local_contra_of_comb_seq_with_mbs g card_of_finite_subsets Higman's_Hh Higman's_Hex Higman's_Hg Higman's_H Higman's_Hbp

-- end

-- check Higman's_local_contradition

-- definition ClassB : Type := {x : finite_subsets Q | ∃ i, B i = x}

-- definition oB (b1 : ClassB) (b2 : ClassB) : Prop := ofs (elt_of b1) (elt_of b2)

-- theorem oB_refl (q : ClassB) : oB q q := ofs_refl (elt_of q)

-- theorem oB_trans (a b c : ClassB) (H1 : oB a b) (H2 : oB b c) : oB a c :=
-- !ofs_trans H1 H2

--     section
--     -- Suppose there exists a bad sequence of objects in ClassB. We show that we can construct a g : ℕ → ℕ such that ¬ is_good (B ∘ g) o. Then we can apply 'exists_sub_bad'. We cannot directly apply this theorem because ClassB is a type distinct from finite_subsets Q.
--     parameter HfB : ∃ f, ¬ is_good f oB

--     private definition f' : ℕ → ClassB := some HfB

--     private theorem bad_f' : ¬ is_good f' oB := some_spec HfB

--     private definition g' (n : ℕ) := elt_of (f' n)

--     theorem exists_bad_B_seq : ¬ is_good g' ofs :=
--     suppose is_good g' ofs,
--     obtain (i j) hg', from this,
--     have ofs (elt_of (f' i)) (elt_of (f' j)), from and.right hg',
--     have is_good f' oB, from exists.intro i (exists.intro j (and.intro (and.left hg') this)),
--     bad_f' this

--     private definition g (n : ℕ) : ℕ := 
--     have ∃ i, B i = g' n, from has_property (f' n),
--     some this

--     private theorem comp_eq_g' : B ∘ g = g' :=
--     have ∀ x, B (g x) = g' x, from take x, some_spec (has_property (f' x)),
--     funext this

--     private theorem bad_comp : ¬ is_good (B ∘ g) ofs := 
--     have ¬ is_good g' ofs, from exists_bad_B_seq,
--     by+ rewrite -comp_eq_g' at this;exact this

--     theorem exists_sub_bad_B_seq : ∃ h : ℕ → ℕ, ¬ is_good (B ∘ h) ofs ∧ ∀ i : ℕ, h 0 ≤ h i := exists_sub_bad B g ofs bad_comp

--     end

-- theorem oB_is_good : ∀ f, is_good f oB :=
-- by_contradiction
-- (suppose ¬ ∀ f, is_good f oB,
-- have ∃ f, ¬ is_good f oB, from exists_not_of_not_forall this,
-- have ∃ h : ℕ → ℕ, ¬ is_good (B ∘ h) ofs ∧ ∀ i : ℕ, h 0 ≤ h i, from exists_sub_bad_B_seq this,
-- Higman's_local_contradition this)

-- definition wqo_ClassB [instance] : wqo ClassB := wqo.mk oB oB_refl oB_trans oB_is_good

-- definition wqo_prod_Q_ClassB [instance] : wqo (Q × ClassB) := wqo_prod

-- theorem good_prod_Q_ClassB : ∀ f : ℕ → Q × ClassB, is_good f (o_for_pairs wqo.le oB) := wqo.is_good

-- lemma B_refl (n : ℕ) : ∃ i, B i = B n := exists.intro n rfl

-- definition fB (n : ℕ) : ClassB := tag (B n) (B_refl n)

-- private definition p (n : ℕ) : Q × ClassB := (qn n, fB n)

-- theorem good_p : is_good p (o_for_pairs wqo.le oB) := good_prod_Q_ClassB p

-- theorem Hij : ∃ i j, i < j ∧ (wqo.le (qn i) (qn j) ∧ oB (fB i) (fB j)) := good_p

-- theorem exists_embeds : ∃ i j, i < j ∧ ofs (Higman's_mbs i) (Higman's_mbs j) :=
-- obtain (i j) hij, from good_p,
-- have oB (fB i) (fB j), from and.right (and.right hij),
-- obtain f₁ hf1, from this,
-- have injf₁ : inj_from_to f₁ (elt_of (B i)) (elt_of (B j)), from and.left hf1, 
-- have ∀ a : Q, a ∈ elt_of (B i) → wqo.le a (f₁ a) ∧ f₁ a ∈ elt_of (B j), from and.right hf1, 
-- let f₂ (q : Q) : Q := if q = qn i then qn j else f₁ q in
-- have nondescending : ∀ a : Q, a ∈ elt_of (Higman's_mbs i) → wqo.le a (f₂ a) ∧ f₂ a ∈ elt_of (Higman's_mbs j), from take a, assume Ha, 
--   have Hor : a = qn i ∨ a ∈ elt_of (B i), by+ rewrite -(ins_B_pairs i) at Ha;exact Ha,
--   begin+ cases (decidable.em (a = qn i)) with [H1, H2], 
--   split, rewrite (if_pos H1), rewrite H1,
--   exact and.left (and.right hij),rewrite (if_pos H1), apply qn_in_mbs,
--   split, have conj : wqo.le a (f₂ a) ∧ f₂ a ∈ elt_of (B j), by rewrite (if_neg H2),
--   apply and.right hf1, apply or_resolve_right Hor H2, exact and.left conj,
--   have conj : wqo.le a (f₂ a) ∧ f₂ a ∈ elt_of (B j), by rewrite (if_neg H2),
--   apply and.right hf1, apply or_resolve_right Hor H2,
--   exact (sub_B_mbs j) (and.right conj) end,
-- have Hmapsto : ∀ a, a ∈ elt_of (Higman's_mbs i) → f₂ a ∈ elt_of (Higman's_mbs j), from 
--   take a, assume Ha, and.right (nondescending a Ha),
-- have ∀ a₁ a₂, a₁ ∈ elt_of (Higman's_mbs i) → a₂ ∈ elt_of (Higman's_mbs i) → f₂ a₁ = f₂ a₂ → a₁ = a₂, from 
--   take a₁ a₂, assume Ha₁, assume Ha₂, assume Heq,
--   have Hora₁ : a₁ = qn i ∨ a₁ ∈ elt_of (B i), by+ rewrite -(ins_B_pairs i) at Ha₁;exact Ha₁,
--   have Hora₂ : a₂ = qn i ∨ a₂ ∈ elt_of (B i), by+ rewrite -(ins_B_pairs i) at Ha₂;exact Ha₂,
--   by_cases
--   (assume Hpos : a₁ = qn i, -- level-1 subcase // pos
--    have eq21j : f₂ a₁ = qn j, from if_pos Hpos,
--    by_contradiction
--    (suppose a₁ ≠ a₂,
--     have neq : qn i ≠ a₂, by+ rewrite Hpos at this;exact this,
--     have eq2212 : f₂ a₂ = f₁ a₂, from if_neg (ne.symm neq),
--     have qn j ∈ elt_of (B j), begin+ rewrite [-eq21j, Heq, eq2212], apply and.left injf₁,
--     exact or_resolve_right Hora₂ (ne.symm neq) end,
--     (qn_not_in_Bn j) this))
--   (assume Hneg, -- level-1 subcase // neg
--    have eq2111 : f₂ a₁ = f₁ a₁, from if_neg Hneg,
--    have a1inBi :  a₁ ∈ elt_of (B i), from or_resolve_right Hora₁ Hneg, 
--    by_cases
--      (assume Hposa₂ : a₂ = qn i, -- level-2 subcase // pos
--       have eq21j : f₂ a₂ = qn j, from if_pos Hposa₂,
--       by_contradiction
--       (suppose a₁ ≠ a₂,
--        have neq2 : a₁ ≠ qn i, by+ rewrite Hposa₂ at this;exact this,
--        have eq2111 : f₂ a₁ = f₁ a₁, from if_neg neq2,
--        have qn j ∈ elt_of (B j), 
--        begin+ rewrite [-eq21j, -Heq, eq2111], apply and.left injf₁, 
--        exact or_resolve_right Hora₁ neq2 end,
--        (qn_not_in_Bn j) this))
--      (assume Hnega₂, -- level-2 subcase // neg
--       have eq2212 : f₂ a₂ = f₁ a₂, from if_neg Hnega₂,
--       have f₁ a₁ = f₂ a₂, by+ rewrite eq2111 at Heq;exact Heq,
--       have eq1112 : f₁ a₁ = f₁ a₂, from eq.trans this eq2212,
--       have a₂ ∈ elt_of (B i), from or_resolve_right Hora₂ Hnega₂, 
--       (and.right injf₁) a₁ a₂ a1inBi this eq1112)),
-- have inj_from_to f₂ (elt_of (Higman's_mbs i)) (elt_of (Higman's_mbs j)), from and.intro Hmapsto this,
-- have ofs (Higman's_mbs i) (Higman's_mbs j), from exists.intro f₂ (and.intro this nondescending),
-- exists.intro i (exists.intro j (and.intro (and.left hij) this))

-- theorem goodness_of_Higman's_mbs : is_good Higman's_mbs ofs := exists_embeds

-- theorem Higman's_contradiction : false := badness_of_Higman's_mbs goodness_of_Higman's_mbs

-- end

-- check Higman's_contradiction

-- variable {Q : Type}
-- variable [wqo Q]

-- theorem ofs_is_good : ∀ f : ℕ → finite_subsets Q , is_good f ofs := 
-- by_contradiction
-- (suppose ¬ ∀ f, is_good f ofs,
-- have ∃ f, ¬ is_good f ofs, from exists_not_of_not_forall this,
-- Higman's_contradiction this)

-- definition wqo_finite_subsets [instance] : wqo (finite_subsets Q) :=
-- wqo.mk ofs ofs_refl ofs_trans ofs_is_good

-- example : @wqo.le (finite_subsets Q) _ = ofs := rfl

-- check wqo_finite_subsets

end kruskal
