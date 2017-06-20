import .lemmas .dickson
open classical nat function prod set subtype list

noncomputable theory

theorem sub_gt_of_gt_ge {a b c : ℕ} (H1 : a > b) (H2 : b ≥ c) : a - c > b - c :=
have c ≤ a, from le_of_lt (lt_of_le_of_lt H2 H1),
have eq₁ : a - c + c = a, from nat.sub_add_cancel this,
have eq₂ : b - c + c = b, from nat.sub_add_cancel H2,
have b ≤ a, from le_of_lt H1,
have b - c ≤ a - c, from nat.sub_le_sub_right this c,
or.elim (nat.lt_or_eq_of_le this)
(assume Hl, Hl)
(assume Hr, have refl : a > a, by super,
 absurd refl (lt_irrefl a))

namespace kruskal

#check good_pairs

section
parameter {A : Type}
parameter f : ℕ → A
parameter g : ℕ → ℕ
parameter o : A → A → Prop
parameter H : ¬ is_good (f ∘ g) o

definition ran_g : set ℕ := {x : ℕ | ∃ i, g i = x}

theorem ne_empty_ran : ran_g ≠ ∅ := ne_empty_of_mem ⟨0,rfl⟩

private definition min : ℕ := least ran_g ne_empty_ran

definition index_of_min : ℕ :=
have min ∈ ran_g, from least_is_mem ran_g ne_empty_ran,
some this 

theorem minimality_of_min (n : ℕ) : g index_of_min ≤ g n :=
have H1 : g index_of_min = min, from some_spec (least_is_mem ran_g ne_empty_ran),
have least ran_g ne_empty_ran ≤ g n, from minimality _ (g n) ⟨n,rfl⟩,
begin simp [H1], exact this end

private definition h (n : ℕ) : ℕ := g (index_of_min + n)

theorem exists_sub_bad : ∃ h : ℕ → ℕ, ¬ is_good (f ∘ h) o ∧ ∀ i : ℕ, h 0 ≤ h i :=
have badness : ¬ is_good (f ∘ h) o, from
   suppose is_good (f ∘ h) o,
   let ⟨i,j,hij⟩ := this in
   have index_of_min + i < index_of_min + j, from add_lt_add_left (and.left hij) _,
   have is_good (f ∘ g) o, from ⟨index_of_min + i,⟨index_of_min + j,⟨this,hij^.right⟩⟩⟩,
   H this,
have ∀ i : ℕ, h 0 ≤ h i, from λ i, minimality_of_min (index_of_min + i),
⟨h,⟨badness,this⟩⟩

end

definition extends_at {A : Type} (n : ℕ) (f : ℕ → A) (g : ℕ → A) : Prop := ∀ m ≤ n, g m = f m

theorem extends_at.refl {A : Type} {n : ℕ} {f : ℕ → A} : extends_at n f f := λ m H, rfl

theorem extends_at.trans {A : Type} {n m : ℕ} {f g h: ℕ → A} (H1 : extends_at n f g) (H2 : extends_at m g h) (H3 : n ≤ m) : 
  extends_at n f h := λ k H, 
have g k = f k, from H1 k H,
have k ≤ m, from nat.le_trans H H3,
have h k = g k, from H2 k this,
by super

theorem least_seq_at_n {S : set (ℕ → ℕ)} (H : S ≠ ∅) (n : ℕ) : 
∃ f : ℕ → ℕ, f ∈ S ∧ ∀ g : ℕ → ℕ, g ∈ S → f n ≤ g n :=
let T : set ℕ := {x | ∃ f :ℕ → ℕ, f ∈ S ∧ f n = x} in
have ∃ f, f ∈ S, from exists_mem_of_ne_empty H,
let ⟨f,h⟩ := this in
have nemp : T ≠ ∅, from ne_empty_of_mem ⟨f,⟨h,rfl⟩⟩,
let a := least T nemp in
have a ∈ T, from least_is_mem T nemp,
let ⟨f',h⟩ := this in
have ∀ g : ℕ → ℕ, g ∈ S → f' n ≤ g n, from λ g Hg, 
  have a ≤ g n, from minimality _ _ ⟨g,⟨Hg,rfl⟩⟩, 
  by super,
⟨f',⟨h^.left, this⟩⟩

section
parameter {A : Type}
parameter {P : (ℕ → A) → Prop}
parameter g : A → ℕ
parameter H : ∃ f : ℕ → A, P f

definition colle : set (ℕ → A) := {f | P f}

lemma nonempty_colle : colle ≠ ∅ :=  let ⟨a,h⟩ := H in ne_empty_of_mem h

definition S : set (ℕ → ℕ) := image (λ f, g ∘ f) colle

lemma nonempty_S : S ≠ ∅ := image_nonempty nonempty_colle

theorem exists_min_func (n : ℕ) : ∃ f : ℕ → ℕ, f ∈ S ∧ ∀ g : ℕ → ℕ, g ∈ S → f n ≤ g n := least_seq_at_n nonempty_S n

definition min_func (n : ℕ) : ℕ → A := 
let fc := some (exists_min_func n) in
have fc ∈ S ∧ ∀ g : ℕ → ℕ, g ∈ S → fc n ≤ g n, from (some_spec (exists_min_func n)),
some this^.left

theorem min_func_property (n : ℕ) : P (min_func n) :=
let fc := some (exists_min_func n) in
let ⟨l,r⟩ := some_spec (exists_min_func n) in
have min_func n ∈ colle ∧ (λ f, g ∘ f) (min_func n) = fc, from some_spec l ,
this^.left

theorem min_func_minimality (f : ℕ → A) (Hp : P f) (n : ℕ) : g (min_func n n) ≤ g (f n) := 
let fc := some (exists_min_func n) in
let ⟨l,r⟩ := some_spec (exists_min_func n) in
have min_func n ∈ colle ∧ (λ f, g ∘ f) (min_func n) = fc, from some_spec l,
have (λ f, g ∘ f) (min_func n) = fc, from this^.right, 
have eq2 : (λ f, g ∘ f) (min_func n) n = fc n, by rw this, 
have Hr : ∀ g : ℕ → ℕ, g ∈ S → fc n ≤ g n, from (some_spec (exists_min_func n))^.right,
have le : fc n ≤ (λ f, g ∘ f) f n, from Hr _ ⟨f,⟨Hp,rfl⟩⟩,
have (λ f, g ∘ f) (min_func n) n ≤ (λ f, g ∘ f) f n, by rw -eq2 at le;exact le,
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
(let f₀ := min_func g H 0 in
 have P f₀, from min_func_property g H 0,
 ⟨f₀,this⟩)
(λ pred h',
let f' := h'.1 in
have H1 : extends_at pred f' f', from extends_at.refl,
have H2 : P f', from h'.2,
have HP : ∃ f, extends_at pred f' f ∧ P f, from ⟨f',⟨H1,H2⟩⟩,
let fn := min_func g HP (succ pred) in
have extends_at pred f' fn ∧ P fn, from min_func_property g HP (succ pred),
have P fn, from this^.right,
⟨fn,this⟩)

  section
  parameter n : ℕ
  definition helper_elt := (mbs_helper n).1
  definition helper_succ := (mbs_helper (succ n)).1
  lemma helper_ext_refl : extends_at n helper_elt helper_elt := extends_at.refl
  lemma helper_has_property : P helper_elt := (mbs_helper n).2
  lemma helper_inner_hyp : ∃ g, extends_at n helper_elt g ∧ P g := ⟨helper_elt, ⟨helper_ext_refl, helper_has_property⟩⟩
  theorem succ_ext_of_mbs_helper : extends_at n helper_elt helper_succ := (min_func_property g helper_inner_hyp (succ n))^.left
  end

theorem ext_of_mbs_helper (n : ℕ) : ∀ m, m ≤ n → extends_at m  (mbs_helper m).1 (mbs_helper n).1 :=
nat.rec_on n
(take m, assume H, 
have eq : m = 0, from eq_zero_of_le_zero H,
have extends_at 0 (mbs_helper 0).1 (mbs_helper 0).1, from extends_at.refl,
by simp [eq,this])
(λ a IH m H,
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
have i ≤ j, from le_of_lt_or_eq (or.inl h^.left),
have ext : extends_at i (seq_of_bad_seq i).1 (seq_of_bad_seq j).1, from ext_of_seq_of_bad_seq j i this,
have i ≤ i, from nat.le_refl i,
have (seq_of_bad_seq j).1 i = (minimal_bad_seq i), from ext i this,
have o ((seq_of_bad_seq j).1 i) (minimal_bad_seq j), by rw this; exact h^.right,
have i < j ∧ o ((seq_of_bad_seq j).1 i) ((seq_of_bad_seq j).1 j), from ⟨h^.left, this⟩,
have good : is_good (seq_of_bad_seq j).1 o, from ⟨i,⟨j, this⟩⟩,
have ¬ is_good (seq_of_bad_seq j).1 o, from (seq_of_bad_seq j).2, 
this good

theorem minimality_of_mbs_0 (f : ℕ → A) (Hf : ¬ is_good f o) : g (minimal_bad_seq 0) ≤ g (f 0) := min_func_minimality g H f Hf 0

theorem minimality_of_mbs (n : ℕ) (f : ℕ → A) (H1 : extends_at n minimal_bad_seq f ∧ ¬ is_good f o) : g (minimal_bad_seq (succ n)) ≤ g (f (succ n)) := 
have Hl : ∀ m, m ≤ n →  f m = (bad_seq_elt n) m, from 
  λ m Hle, have f m = minimal_bad_seq m, from H1^.left m Hle,
  have bad_seq_elt n m = minimal_bad_seq m, from congruence_of_seq_of_bad_seq Hle,
  by super, --by+ simp,
have ins_P : extends_at n (bad_seq_elt n) f ∧ ¬ is_good f o, from ⟨Hl, H1^.right⟩,
have ineq : g (min_func g (bad_seq_inner_hyp n) (succ n) (succ n)) ≤ g (f (succ n)), from min_func_minimality g (bad_seq_inner_hyp n) f ins_P (succ n), 
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

definition comb (n : ℕ) : Q := if n < h 0 then f n else g (n - h 0)

theorem g_part_of_comb (H : (h 0) = 0) : ∀ x, comb x = g x :=
λ n, have ¬ n < h 0, by rw H; apply not_lt_zero ,
have comb n = g (n - (h 0)), from if_neg this,
by simp [this, H]

include Hh

theorem badness_of_comb : ¬ is_good comb o := 
λ good, let ⟨i,j,hw⟩ := good in
by_cases
(assume Hposi : i < h 0, 
  have eq1i : comb i = f i, from if_pos Hposi,
  by_cases 
  (suppose j < h 0, 
    have eq1j : comb j = f j, from if_pos this, 
    have o (f i) (f j),by rw [-eq1j,-eq1i]; exact hw^.right,
    have is_good f o, from ⟨i, ⟨j,⟨hw^.left,this⟩⟩⟩,
    show _, from Hf this)
  (suppose ¬ j < h 0,
    have eq2j : comb j = g (j - (h 0)), from if_neg this, 
    have o (f i) (g (j - (h 0))), by rw [-eq2j,-eq1i]; exact hw^.right,
    have Hr : o (f i) (f (h (j - (h 0)))), from H _ _ this,
    have i < h (j - (h 0)), from lt_of_lt_of_le Hposi (Hh _),
    have is_good f o, from ⟨i, ⟨h (j - h 0), ⟨this, Hr⟩⟩⟩,
    show _, from Hf this))
(assume Hnegi, 
  have eq2i : comb i = g (i - h 0), from if_neg Hnegi,
  by_cases
  (suppose j < h 0,
    have j < i, from lt_of_lt_of_le this (le_of_not_gt Hnegi),
    show _, from (not_lt_of_gt hw^.left) this)
  (suppose ¬ j < h 0, 
    have eq2j : comb j = g (j - h 0), from if_neg this,
    have Hr2 : o (g (i - h 0)) (g (j - h 0)), by rw [-eq2i,-eq2j]; exact hw^.right,
    have i - h 0 < j - h 0, from sub_gt_of_gt_ge hw^.left (le_of_not_gt Hnegi),
    have is_good g o, from ⟨(i - h 0), ⟨(j - h 0),⟨this, Hr2⟩⟩⟩,
    show _, from Hg this))

end

section
-- further assume that f is a minimal bad sequence and card (g 0) < card (f (h 0)) 
-- In other words, this section says, assuming that there is a bad sequence of Q, if g is a bad sequence such that H holds, then there is a contradiction. 
parameter {Q :Type}
parameter {o : Q → Q → Prop}
parameters {g : ℕ → Q}
parameter h : ℕ → ℕ
parameter m : Q → ℕ -- a measure of cardinality
parameter Hh : ∀ i, h 0 ≤ h i
parameter Hex : ∃ f, ¬ is_good f o
parameter Hg : ¬ is_good g o
parameter H : ∀ i j, o (minimal_bad_seq m Hex i) (g (j - h 0)) → o (minimal_bad_seq m Hex i) ((minimal_bad_seq m Hex) (h (j - h 0)))
parameter Hbp : m (g 0) < m (minimal_bad_seq m Hex (h 0))

definition comb_seq_with_mbs := comb (minimal_bad_seq m Hex) g h

theorem g_part_of_comb_seq_with_mbs (H1 : (h 0) = 0) : ∀ x, comb_seq_with_mbs x = g x := 
begin apply g_part_of_comb, assumption end

theorem badness_of_comb_seq_with_mbs : ¬ is_good comb_seq_with_mbs o := 
badness_of_comb (minimal_bad_seq m Hex) g h Hh (badness_of_mbs m Hex) Hg H

theorem comb_seq_extends_mbs_at_pred_bp (H : h 0 ≠ 0): extends_at (pred (h 0)) (minimal_bad_seq m Hex) comb_seq_with_mbs := 
λ m Hm, if_pos (or_resolve_left (lt_of_le_pred Hm) H)

lemma comb_seq_h0 : comb_seq_with_mbs (h 0) = g 0 := 
have comb_seq_with_mbs (h 0) = g (h 0 - h 0), begin apply if_neg, rw lt_self_iff_false, trivial end,
by simp [this,nat.sub_self]

include Hbp Hex

theorem local_contra_of_comb_seq_with_mbs : false := 
by_cases
(suppose eq0 : h 0 = 0, 
have eq : comb_seq_with_mbs 0 = g 0, begin apply g_part_of_comb_seq_with_mbs, assumption end,
have m (comb_seq_with_mbs 0) < m (minimal_bad_seq m Hex (h 0)), by rw -eq at Hbp;exact Hbp,
have le : m (comb_seq_with_mbs 0) < m (minimal_bad_seq m Hex 0), by super,
have m (minimal_bad_seq m Hex 0) ≤ m (comb_seq_with_mbs 0), from minimality_of_mbs_0 m Hex comb_seq_with_mbs badness_of_comb_seq_with_mbs,
(not_le_of_gt le) this)
(assume Hneg, 
have le : m (minimal_bad_seq m Hex (succ (pred (h 0)))) ≤  m (comb_seq_with_mbs (succ (pred (h 0)))), from minimality_of_mbs m _ _ _ ⟨begin apply comb_seq_extends_mbs_at_pred_bp, exact Hneg end,badness_of_comb_seq_with_mbs⟩,
have h 0 > 0, from nat.pos_of_ne_zero Hneg,
have succ (pred (h 0)) = h 0, from succ_pred_of_pos this,
have m (minimal_bad_seq m Hex (h 0)) ≤ m (comb_seq_with_mbs (h 0)), by rw this at le;exact le,
have m (minimal_bad_seq m Hex (h 0)) ≤ m (g 0), by rw comb_seq_h0 at this;exact this,
have ¬ m (g 0) < m (minimal_bad_seq m Hex (h 0)), from not_lt_of_ge this,  
this Hbp)

end

section
variable {α : Type}

inductive sublist' [has_le α]: list α → list α → Prop
| slnil : sublist' [] []
| cons (l₁ l₂ a) : sublist' l₁ l₂ → sublist' l₁ (a::l₂)
| cons2 (l₁ l₂ a b) : a ≤ b → sublist' l₁ l₂ → sublist' (a::l₁) (b::l₂)

infix ` <++ `:50 := sublist'

@[simp] lemma nil_sublist' [has_le α] : Π (l : list α), [] <++ l
| []       := sublist'.slnil
| (a :: l) := sublist'.cons _ _ a (nil_sublist' l)

@[simp] lemma sublist'.refl [quasiorder α] : Π (l : list α), l <++ l
| []       := sublist'.slnil
| (a :: l) := sublist'.cons2 _ _ a _ (quasiorder.refl a) (sublist'.refl l)

open sublist'

lemma sublist'.trans [quasiorder α] : Π {l₁ l₂ l₃ : list α}, l₁ <++ l₂ → l₂ <++ l₃ → l₁ <++ l₃
| ._ ._ ._ (slnil) (slnil) := nil_sublist' nil
| ._ ._ ._ (slnil) (cons ._ l₃' a h) := nil_sublist' _
| ._ ._ ._ (cons l₁ l₂' a h) (cons ._ l₃' b h') := 
  have l₁ <++ l₃', from sublist'.trans (cons _ _ _ h) h',
  show _, from cons _ _ _ this
| ._ ._ ._ (cons l₁ l₂' a h) (cons2 ._ l₃' ._ b hab h') := 
  have l₁ <++ l₃', from sublist'.trans h h',
  show _, from cons _ _ _ this
| ._ ._ ._ (cons2 l₁' l₂' a b hab h) (cons ._ l₃' c h') := 
  have a :: l₁' <++ b :: l₂', from cons2 _ _ _ _ hab h,
  have a :: l₁' <++ l₃', from sublist'.trans this h',
  show _, from cons _ _ _ this
| ._ ._ ._ (cons2 l₁' l₂' a b hab h) (cons2 ._ l₃' ._ d hbd h') := 
  show _, from cons2 _ _ _ _ (quasiorder.trans hab hbd) (sublist'.trans h h')

lemma sublist'.trans' [quasiorder α] {l₁ l₂ l₃ : list α} (h₁ : l₁ <++ l₂)  (h₂ : l₂ <++ l₃) : l₁ <++ l₃ :=
sublist'.trans h₁ h₂

@[simp] lemma sublist'_cons [quasiorder α](a : α) (l : list α) : l <++ a::l :=
sublist'.cons _ _ _ (sublist'.refl l)


end

section
parameter {Q : Type}
parameter [o : wqo Q]

parameter H : ∃ f : ℕ → list Q, ¬ is_good f sublist'

definition Higman's_mbs (n : ℕ) : list Q := minimal_bad_seq length H n

theorem badness_of_Higman's_mbs : ¬ is_good Higman's_mbs sublist' := badness_of_mbs length H

theorem nonempty_mem_of_mbs (n : ℕ) : Higman's_mbs n ≠ [] := 
λ h, badness_of_Higman's_mbs ⟨n, ⟨succ n,⟨lt_succ_self n,begin rw h, apply nil_sublist' end⟩⟩⟩

definition B_pairs (n : ℕ) : Q × list Q := 
have ∃ p : Q × list Q, Higman's_mbs n = p.1 :: p.2, from ne_nil_desturct (nonempty_mem_of_mbs n),
some this

private definition B (n : ℕ) : list Q := (B_pairs n).2

definition qn (n : ℕ) : Q := (B_pairs n).1

theorem Higman's_mbs_destruct (n : ℕ) : Higman's_mbs n = qn n :: B n :=
some_spec (ne_nil_desturct (nonempty_mem_of_mbs n))

theorem qn_in_mbs (n : ℕ) : qn n ∈ Higman's_mbs n :=
have Higman's_mbs n = qn n :: B n, from some_spec (ne_nil_desturct (nonempty_mem_of_mbs n)),
begin rw this, apply or.inl, reflexivity end

theorem sub_B_mbs (n : ℕ) : B n <++ Higman's_mbs n :=
have B n <++ qn n :: B n, from sublist'.cons _ _ _ (sublist'.refl _),
have Higman's_mbs n = qn n :: B n, from Higman's_mbs_destruct n,
by simph

theorem trans_of_B (i j : ℕ) (H1 : Higman's_mbs i <++ B j) : Higman's_mbs i <++ Higman's_mbs j :=
sublist'.trans H1 (sub_B_mbs j)

theorem len_B_lt_mbs (n : ℕ) : length (B n) < length (Higman's_mbs n) :=
have length (B n) < length (qn n :: B n), by rw length_cons; apply lt_succ_self,
have Higman's_mbs n = qn n :: B n, from Higman's_mbs_destruct n,
by super

section
parameter Hg : ∃ g : ℕ → ℕ, ¬ is_good (B ∘ g) sublist' ∧ ∀ i : ℕ, g 0 ≤ g i

private definition g : ℕ → ℕ := some Hg

theorem Higman's_Hg : ¬ is_good (B ∘ g) sublist' := 
let ⟨l,r⟩ := some_spec Hg in l

theorem Higman's_Hex : ∃ f : ℕ → list Q, ¬ is_good f sublist' := 
⟨(B ∘ g), Higman's_Hg⟩

theorem Higman's_Hh : ∀ i : ℕ, g 0 ≤ g i := (some_spec Hg)^.right

theorem Higman's_H : ∀ i j, Higman's_mbs i <++ (B ∘ g) (j - g 0) → Higman's_mbs i <++ Higman's_mbs (g (j - g 0)) := 
λ i j, λ H1, trans_of_B i (g (j - g 0)) H1

theorem Higman's_Hbp : length (B (g 0)) < length (Higman's_mbs (g 0)) := len_B_lt_mbs (g 0)

theorem Higman's_local_contradition : false := 
local_contra_of_comb_seq_with_mbs g length Higman's_Hh Higman's_Hex Higman's_Hg Higman's_H Higman's_Hbp

end

definition ClassB : Type := {x : list Q // ∃ i, B i = x}

definition oB (b1 : ClassB) (b2 : ClassB) : Prop := b1.val <++ b2.val

theorem oB_refl (q : ClassB) : oB q q := sublist'.refl q.val

theorem oB_trans (a b c : ClassB) (H1 : oB a b) (H2 : oB b c) : oB a c :=
sublist'.trans H1 H2

    section
    parameter HfB : ∃ f, ¬ is_good f oB

    private definition f' : ℕ → ClassB := some HfB

    private theorem bad_f' : ¬ is_good f' oB := some_spec HfB

    private definition g' (n : ℕ) := (f' n).val

    theorem exists_bad_B_seq : ¬ is_good g' sublist' :=
    suppose is_good g' sublist',
    let ⟨i,j,hg'⟩ := this in
    have is_good f' oB, from ⟨i, ⟨j, ⟨hg'^.left, hg'^.right⟩⟩⟩,
    bad_f' this

    private definition g (n : ℕ) : ℕ := 
    have ∃ i, B i = g' n, from (f' n).2,
    some this

    private theorem comp_eq_g' : B ∘ g = g' :=
    have ∀ x, B (g x) = g' x, from λ x, some_spec (f' x).2,
    funext this

    private theorem bad_comp : ¬ is_good (B ∘ g) sublist' := 
    have ¬ is_good g' sublist', from exists_bad_B_seq,
    by rw -comp_eq_g' at this;exact this

    theorem exists_sub_bad_B_seq : ∃ h : ℕ → ℕ, ¬ is_good (B ∘ h) sublist' ∧ ∀ i : ℕ, h 0 ≤ h i := exists_sub_bad B g sublist' bad_comp

    end

theorem oB_is_good : ∀ f, is_good f oB :=
by_contradiction
(suppose ¬ ∀ f, is_good f oB,
have ∃ f, ¬ is_good f oB, from classical.exists_not_of_not_forall this,
have ∃ h : ℕ → ℕ, ¬ is_good (B ∘ h) sublist' ∧ ∀ i : ℕ, h 0 ≤ h i, from exists_sub_bad_B_seq this,
Higman's_local_contradition this)

instance wqo_ClassB : wqo ClassB := wqo.mk (quasiorder.mk (has_le.mk oB) oB_refl oB_trans) oB_is_good

instance wqo_prod_Q_ClassB : wqo (Q × ClassB) := @wqo_prod _ _ o _

theorem good_prod_Q_ClassB : ∀ f : ℕ → Q × ClassB, is_good f (prod_order o.le oB) := wqo.is_good

lemma B_refl (n : ℕ) : ∃ i, B i = B n := ⟨n, rfl⟩

definition fB (n : ℕ) : ClassB := ⟨B n,B_refl n⟩

private definition p (n : ℕ) : Q × ClassB := (qn n, fB n)

theorem good_p : is_good p (prod_order o.le oB) := good_prod_Q_ClassB p

theorem Hij : ∃ i j, i < j ∧ ((qn i) ≤ (qn j) ∧ oB (fB i) (fB j)) := good_p

theorem exists_embeds : ∃ i j, i < j ∧ Higman's_mbs i <++ Higman's_mbs j :=
let ⟨i,j,⟨hijl,⟨hijrl,hijrr⟩⟩⟩ := good_p in
have qn i :: B i <++ qn j :: B j, from sublist'.cons2 _ _ _ _ hijrl hijrr,
have Higman's_mbs i = qn i :: B i, from Higman's_mbs_destruct i,
have Higman's_mbs j = qn j :: B j, from Higman's_mbs_destruct j,
have Higman's_mbs i <++ Higman's_mbs j, by simph,
⟨i,j,⟨hijl,this⟩⟩

theorem Higman's_contradiction : false := badness_of_Higman's_mbs exists_embeds

end

variable {Q : Type}
variable [wqo Q]

theorem good_sublist : ∀ f : ℕ → list Q , is_good f sublist' := 
by_contradiction
(suppose ¬ ∀ f, is_good f sublist',
have ∃ f, ¬ is_good f sublist', from classical.exists_not_of_not_forall this,
Higman's_contradiction this)

def wqo_list : wqo (list Q) :=
⟨⟨⟨sublist'⟩,sublist'.refl,λ a b c h₁ h₂,sublist'.trans' h₁ h₂⟩,good_sublist⟩


end kruskal
