import ..library_dev.data.list.set ..library_dev.data.list.perm .quot .misc
open list subtype nat

definition nodup_list (A : Type) := {l : list A // nodup l}

variable {A : Type}

definition to_nodup_list_of_nodup {l : list A} (n : nodup l) : nodup_list A := ⟨l,n⟩

definition to_nodup_list [decidable_eq A] (l : list A) : nodup_list A :=
@to_nodup_list_of_nodup A (erase_dup l) (nodup_erase_dup l)

private definition eqv (l₁ l₂ : nodup_list A) :=
perm (l₁.1) (l₂.1)

local infix ~ := eqv

private definition eqv.refl (l : nodup_list A) : l ~ l :=
perm.refl _

private definition eqv.symm {l₁ l₂ : nodup_list A} : l₁ ~ l₂ → l₂ ~ l₁ :=
perm.symm

private definition eqv.trans {l₁ l₂ l₃ : nodup_list A} : l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃ :=
perm.trans

attribute [instance]
definition finset.nodup_list_setoid (A : Type) : setoid (nodup_list A) :=
setoid.mk (@eqv A) (mk_equivalence (@eqv A) (@eqv.refl A) (@eqv.symm A) (@eqv.trans A))

definition finset (A : Type) : Type :=
quotient (finset.nodup_list_setoid A)


namespace finset

-- give finset notation higher priority than set notation, so that it is tried first
protected definition prio : num := num.succ std.priority.default

definition to_finset_of_nodup (l : list A) (n : nodup l) : finset A :=
⟦to_nodup_list_of_nodup n⟧

definition to_finset [decidable_eq A] (l : list A) : finset A :=
⟦to_nodup_list l⟧

-- lemma to_finset_eq_of_nodup [decidable_eq A] {l : list A} (n : nodup l) :
--   to_finset_of_nodup l n = to_finset l :=
-- have P : to_nodup_list_of_nodup n = to_nodup_list l, from
--   begin
--     rewrite [↑to_nodup_list, ↑to_nodup_list_of_nodup],
--     congruence,
--     rewrite [erase_dup_eq_of_nodup n]
--   end,
-- quot.sound (eq.subst P !setoid.refl)

attribute [instance]
definition has_decidable_eq [decidable_eq A] : decidable_eq (finset A) :=
λ s₁ s₂, quot.rec_on_subsingleton₂ s₁ s₂
  (λ l₁ l₂,
     match perm.decidable_perm (l₁.1) (l₂.1) with
     | decidable.is_true e := decidable.is_true (quot.sound e)
     | decidable.is_false n := decidable.is_false (λ e : ⟦l₁⟧ = ⟦l₂⟧, absurd (quot.exact e) n)
     end)

definition mem (a : A) (s : finset A) : Prop :=
quot.lift_on s (λ l, a ∈ l.1)
 (λ l₁ l₂ (e : l₁ ~ l₂), propext (iff.intro
   (λ ainl₁, perm.mem_perm e ainl₁)
(λ ainl₂, perm.mem_perm (perm.symm e) ainl₂)))

infix [priority finset.prio] ∈ := mem
notation [priority finset.prio] a ∉ b := ¬ mem a b

theorem mem_of_mem_list {a : A} {l : nodup_list A} : a ∈ l.1 → a ∈ ⟦l⟧ :=
λ ainl, ainl

theorem mem_list_of_mem {a : A} {l : nodup_list A} : a ∈ ⟦l⟧ → a ∈ l.1 :=
λ ainl, ainl

attribute [instance]
definition decidable_mem [h : decidable_eq A] : ∀ (a : A) (s : finset A), decidable (a ∈ s) :=
λ a s, quot.rec_on_subsingleton s
  (λ l, match list.decidable_mem a l.1 with
        | decidable.is_true p := decidable.is_true (mem_of_mem_list p)
        | decidable.is_false n := decidable.is_false (λ p, absurd (mem_list_of_mem p) n)
end)

theorem mem_to_finset [decidable_eq A] {a : A} {l : list A} : a ∈ l → a ∈ to_finset l :=
λ ainl, mem_erase_dup ainl

theorem mem_to_finset_of_nodup {a : A} {l : list A} (n : nodup l) : a ∈ l → a ∈ to_finset_of_nodup l n :=
λ ainl, ainl

/- extensionality -/
theorem ext {s₁ s₂ : finset A} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ e, quot.sound (perm.perm_ext (l₁.2) (l₂.2) e))

/- empty -/
definition empty : finset A :=
to_finset_of_nodup [] nodup_nil

-- notation [priority finset.prio] `∅` := empty _

attribute [simp]
theorem not_mem_empty (a : A) : a ∉ empty :=
λ aine, aine

attribute [simp]
theorem mem_empty_iff (x : A) : mem x empty ↔ false :=
iff_false_intro (not_mem_empty _)


theorem mem_empty_eq (x : A) : mem x empty = false :=
propext (mem_empty_iff _)

theorem eq_empty_of_forall_not_mem {s : finset A} (H : ∀x, ¬ x ∈ s) : s = empty :=
ext (λ x, iff_false_intro (H x))

-- /- universe -/
-- definition univ [h : fintype A] : finset A :=
-- to_finset_of_nodup (@fintype.elems A h) (@fintype.unique A h)

-- theorem mem_univ [fintype A] (x : A) : x ∈ univ :=
-- fintype.complete x

-- theorem mem_univ_eq [fintype A] (x : A) : x ∈ univ = true := propext (iff_true_intro !mem_univ)

/- card -/
definition card (s : finset A) : nat :=
quot.lift_on s
  (λ l, length l.1)
  (λ l₁ l₂ p, perm.length_eq_length_of_perm p)

theorem card_empty : card (@empty A) = 0 := rfl

lemma ne_empty_of_card_eq_succ {s : finset A} {n : nat} : card s = succ n → s ≠ empty :=
begin intros, intro eq, rw [eq] at a, contradiction end

/- insert -/
section insert
variable [h : decidable_eq A]
include h


definition insert (a : A) (s : finset A) : finset A :=
quot.lift_on s
  (λ l, to_finset_of_nodup (insert a l.1) (nodup_insert l.2)) -- implicit 'a'
  (λ (l₁ l₂ : nodup_list A) (p : l₁ ~ l₂), quot.sound (perm.perm_insert a p))

-- set builder notation
-- notation [priority finset.prio] `'{`:max a:(foldr `, ` (x b, insert x b) ∅) `}`:0 := a

theorem mem_insert (a : A) (s : finset A) : a ∈ insert a s :=
quot.induction_on s
 (λ l : nodup_list A, mem_to_finset_of_nodup _ (list.mem_insert_self _ _))

theorem mem_insert_of_mem {a : A} {s : finset A} (b : A) : a ∈ s → a ∈ insert b s :=
quot.induction_on s
 (λ (l : nodup_list A) (ainl : a ∈ ⟦l⟧), mem_to_finset_of_nodup _ (list.mem_insert_of_mem ainl))

theorem eq_or_mem_of_mem_insert {x a : A} {s : finset A} : x ∈ insert a s → x = a ∨ x ∈ s :=
quot.induction_on s (λ l : nodup_list A, λ H, list.eq_or_mem_of_mem_insert H)

theorem mem_of_mem_insert_of_ne {x a : A} {s : finset A} (xin : x ∈ insert a s) : x ≠ a → x ∈ s :=
or_resolve_right (eq_or_mem_of_mem_insert xin)

theorem mem_insert_iff (x a : A) (s : finset A) : x ∈ insert a s ↔ (x = a ∨ x ∈ s) :=
iff.intro eq_or_mem_of_mem_insert 
(λ h, or.elim h (λ l, by rw l; apply mem_insert) (λ r, mem_insert_of_mem _ r))

theorem mem_insert_eq (x a : A) (s : finset A) : x ∈ insert a s = (x = a ∨ x ∈ s) :=
propext (mem_insert_iff _ _ _)

theorem mem_singleton_iff (x a : A) : x ∈ insert a empty ↔ (x = a) :=
by rewrite [mem_insert_eq, mem_empty_eq, or_false]

theorem mem_singleton (a : A) : a ∈ insert a empty := mem_insert a empty

theorem mem_singleton_of_eq {x a : A} (H : x = a) : x ∈ insert a empty :=
by rewrite H; apply mem_insert

theorem eq_of_mem_singleton {x a : A} (H : x ∈ insert a empty) : x = a := iff.mp (mem_singleton_iff _ _) H

theorem eq_of_singleton_eq {a b : A} (H : insert a empty = insert b empty) : a = b :=
have a ∈ insert b empty, by rewrite -H; apply mem_singleton,
eq_of_mem_singleton this

-- #check @eq.substr

theorem insert_eq_of_mem {a : A} {s : finset A} (H : a ∈ s) : insert a s = s :=
ext (λ x, iff.intro (λ l, or.elim (eq_or_mem_of_mem_insert l) 
    (λll, by rw ll;exact H) (λ rr, rr)) 
(λ r, mem_insert_of_mem _ r))

theorem singleton_ne_empty (a : A) : insert a empty ≠ empty :=
begin
  intro H,
  apply not_mem_empty a,
  rewrite -H,
  apply mem_insert
end

-- useful in proofs by induction
theorem forall_of_forall_insert {P : A → Prop} {a : A} {s : finset A}
    (H : ∀ x, x ∈ insert a s → P x) :
  ∀ x, x ∈ s → P x :=
λ x xs, H x ((mem_insert_of_mem _)xs)

theorem insert.comm (x y : A) (s : finset A) : insert x (insert y s) = insert y (insert x s) :=
ext (take a, begin repeat {rw mem_insert_eq},  rw [propext or.left_comm] end)

theorem card_insert_of_mem {a : A} {s : finset A} : a ∈ s → card (insert a s) = card s :=
quot.induction_on s
  (λ (l : nodup_list A) (ainl : a ∈ ⟦l⟧), list.length_insert_of_mem ainl)

theorem card_insert_of_not_mem {a : A} {s : finset A} : a ∉ s → card (insert a s) = card s + 1 :=
quot.induction_on s
  (λ (l : nodup_list A) (nainl : a ∉ ⟦l⟧), list.length_insert_of_not_mem nainl)

theorem card_insert_le (a : A) (s : finset A) :
  card (insert a s) ≤ card s + 1 :=
if H : a ∈ s then by rewrite [card_insert_of_mem H]; apply le_succ
else by rewrite [card_insert_of_not_mem H]

attribute [recursor 6]
protected theorem induction {P : finset A → Prop}
    (H1 : P empty)
    (H2 : ∀ ⦃a : A⦄, ∀{s : finset A}, a ∉ s → P s → P (insert a s)) :
  ∀s, P s :=
take s,
quot.induction_on s
 (take u,
  subtype.rec_on u
   (take l,
    list.rec_on l
      (assume nodup_l, H1)
      (take a l',
        assume IH nodup_al',
        have aux₁: a ∉ l', from not_mem_of_nodup_cons nodup_al',
        have ndl' : nodup l', from nodup_of_nodup_cons nodup_al',
        have p1 : P (quot.mk _ (subtype.mk l' ndl')), from IH ndl',
        have ¬ mem a (quot.mk _ (subtype.mk l' ndl')), from aux₁,
        have P (insert a (quot.mk _ (subtype.mk l' _))), from H2 this p1,
        have hperm : perm (list.insert a l') (a :: l'), from perm.perm_insert_cons_of_not_mem aux₁, 
        begin
          apply @eq.subst _ P _ _ _ this,
          apply quot.sound,
          exact hperm
        end)))

protected theorem induction_on {P : finset A → Prop} (s : finset A)
    (H1 : P empty)
    (H2 : ∀ ⦃a : A⦄, ∀{s : finset A}, a ∉ s → P s → P (insert a s)) :
  P s := finset.induction H1 H2 s

theorem exists_mem_of_ne_empty {s : finset A} : s ≠ empty → ∃ a : A, a ∈ s :=
@finset.induction_on _ _ (λ x, x ≠ empty → ∃ a : A, mem a x) s 
(λ h, absurd rfl h)
(by intros a s nin ih h; existsi a; apply mem_insert)

theorem eq_empty_of_card_eq_zero {s : finset A} : card s = 0 → s = empty :=
@finset.induction_on _ _ (λ x, card x = 0 → x = empty) s 
(λ h, rfl) 
(by intros a s' H1 Ih H; rw (card_insert_of_not_mem H1) at H; contradiction)

end insert

/- erase -/
section erase
variable [h : decidable_eq A]
include h

definition erase (a : A) (s : finset A) : finset A :=
quot.lift_on s
  (λ l, to_finset_of_nodup (erase a l.1) (nodup_erase_of_nodup a l.2))
  (λ (l₁ l₂ : nodup_list A) (p : l₁ ~ l₂), quot.sound (perm.erase_perm_erase_of_perm a p))

theorem not_mem_erase (a : A) (s : finset A) : a ∉ erase a s :=
quot.induction_on s
  (λ l, list.mem_erase_of_nodup _ l.2)

theorem card_erase_of_mem {a : A} {s : finset A} : a ∈ s → card (erase a s) = pred (card s) :=
quot.induction_on s (λ l ainl, list.length_erase_of_mem ainl)

theorem card_erase_of_not_mem {a : A} {s : finset A} : a ∉ s → card (erase a s) = card s :=
quot.induction_on s (λ l nainl, list.length_erase_of_not_mem nainl)

theorem erase_empty (a : A) : erase a empty = empty :=
rfl

theorem ne_of_mem_erase {a b : A} {s : finset A} : b ∈ erase a s → b ≠ a :=
by intros h beqa; subst b; exact absurd h (not_mem_erase _ _)

theorem mem_of_mem_erase {a b : A} {s : finset A} : b ∈ erase a s → b ∈ s :=
quot.induction_on s (λ l bin, mem_of_mem_erase bin)

theorem mem_erase_of_ne_of_mem {a b : A} {s : finset A} : a ≠ b → a ∈ s → a ∈ erase b s :=
quot.induction_on s (λ l n ain, list.mem_erase_of_ne_of_mem n ain)

theorem mem_erase_iff (a b : A) (s : finset A) : a ∈ erase b s ↔ a ∈ s ∧ a ≠ b :=
iff.intro
  (assume H, and.intro (mem_of_mem_erase H) (ne_of_mem_erase H))
(assume H, mem_erase_of_ne_of_mem (and.right H) (and.left H))

theorem mem_erase_eq (a b : A) (s : finset A) : a ∈ erase b s = (a ∈ s ∧ a ≠ b) :=
propext (mem_erase_iff _ _ _)

open decidable
theorem erase_insert {a : A} {s : finset A} : a ∉ s → erase a (insert a s) = s :=
λ anins, finset.ext (λ b, by_cases
  (λ beqa : b = a, iff.intro
    (λ bin, by subst b; exact absurd bin (not_mem_erase _ _))
    (λ bin, by subst b; contradiction))
  (λ bnea : b ≠ a, iff.intro
    (λ bin,
       have b ∈ insert a s, from mem_of_mem_erase bin,
       mem_of_mem_insert_of_ne this bnea)
    (λ bin,
      have b ∈ insert a s, from mem_insert_of_mem _ bin,
mem_erase_of_ne_of_mem bnea this)))

theorem insert_erase {a : A} {s : finset A} : a ∈ s → insert a (erase a s) = s :=
λ ains, finset.ext (λ b, by_cases
  (suppose b = a, iff.intro
    (λ bin, by subst b; assumption)
    (λ bin, by subst b; apply mem_insert))
  (assume neq, iff.intro
    (λ bin, mem_of_mem_erase (mem_of_mem_insert_of_ne bin neq))
(λ bin, mem_insert_of_mem _ (mem_erase_of_ne_of_mem neq bin))))

end erase

section union
variable [h : decidable_eq A]
include h

definition union (s₁ s₂ : finset A) : finset A :=
quot.lift_on₂ s₁ s₂
  (λ l₁ l₂,
    to_finset_of_nodup (list.union l₁.1 l₂.1)
                       (nodup_union_of_nodup_of_nodup l₁.2 l₂.2))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound (perm.perm_union p₁ p₂))

infix [priority finset.prio] ∪ := union

theorem mem_union_left {a : A} {s₁ : finset A} (s₂ : finset A) : a ∈ s₁ → a ∈ s₁ ∪ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₁, list.mem_union_left ainl₁ _)

theorem mem_union_l {a : A} {s₁ : finset A} {s₂ : finset A} : a ∈ s₁ → a ∈ s₁ ∪ s₂ :=
mem_union_left s₂

theorem mem_union_right {a : A} {s₂ : finset A} (s₁ : finset A) : a ∈ s₂ → a ∈ s₁ ∪ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₂, list.mem_union_right _ ainl₂)

theorem mem_union_r {a : A} {s₂ : finset A} {s₁ : finset A} : a ∈ s₂ → a ∈ s₁ ∪ s₂ :=
mem_union_right s₁

theorem mem_or_mem_of_mem_union {a : A} {s₁ s₂ : finset A} : a ∈ s₁ ∪ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₁l₂, list.mem_or_mem_of_mem_union ainl₁l₂)

theorem mem_union_iff (a : A) (s₁ s₂ : finset A) : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
iff.intro
 (λ h, mem_or_mem_of_mem_union h)
 (λ d, or.elim d
   (λ i, mem_union_left _ i)
(λ i, mem_union_right _ i))

theorem mem_union_eq (a : A) (s₁ s₂ : finset A) : (a ∈ s₁ ∪ s₂) = (a ∈ s₁ ∨ a ∈ s₂) :=
propext (mem_union_iff _ _ _)

theorem union_comm (s₁ s₂ : finset A) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
ext (λ a, by repeat {rw mem_union_eq}; exact or.comm)

theorem union_assoc (s₁ s₂ s₃ : finset A) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
ext (λ a, by repeat {rw mem_union_eq}; exact or.assoc)

theorem union_left_comm (s₁ s₂ s₃ : finset A) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
left_comm _ union_comm union_assoc s₁ s₂ s₃

theorem union_right_comm (s₁ s₂ s₃ : finset A) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
right_comm _ union_comm union_assoc s₁ s₂ s₃

theorem union_self (s : finset A) : s ∪ s = s :=
ext (λ a, iff.intro
  (λ ain, or.elim (mem_or_mem_of_mem_union ain) (λ i, i) (λ i, i))
  (λ i, mem_union_left _ i))

theorem union_empty (s : finset A) : s ∪ empty = s :=
ext (λ a, iff.intro
  (suppose a ∈ s ∪ empty, or.elim (mem_or_mem_of_mem_union this) (λ i, i) (λ i, absurd i (not_mem_empty _)))
  (suppose a ∈ s, mem_union_left _ this))

theorem empty_union (s : finset A) : empty ∪ s = s :=
calc empty ∪ s = s ∪ empty : union_comm _ _
     ... = s : union_empty _

theorem insert_eq (a : A) (s : finset A) : insert a s = (insert a empty) ∪ s :=
ext (take x, by rewrite [mem_insert_iff, mem_union_iff, mem_singleton_iff])

theorem insert_union (a : A) (s t : finset A) : insert a (s ∪ t) = insert a s ∪ t :=
by rewrite [insert_eq, insert_eq a s, union_assoc]

end union


/- inter -/
section inter
variable [h : decidable_eq A]
include h

definition inter (s₁ s₂ : finset A) : finset A :=
quot.lift_on₂ s₁ s₂
  (λ l₁ l₂,
    to_finset_of_nodup (list.inter l₁.1 l₂.1)
                       (nodup_inter_of_nodup _ l₁.2))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound (perm.perm_inter p₁ p₂))


infix [priority finset.prio] ∩ := inter

theorem mem_of_mem_inter_left {a : A} {s₁ s₂ : finset A} : a ∈ s₁ ∩ s₂ → a ∈ s₁ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₁l₂, list.mem_of_mem_inter_left ainl₁l₂)

theorem mem_of_mem_inter_right {a : A} {s₁ s₂ : finset A} : a ∈ s₁ ∩ s₂ → a ∈ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₁l₂, list.mem_of_mem_inter_right ainl₁l₂)


theorem mem_inter {a : A} {s₁ s₂ : finset A} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₁ ainl₂, list.mem_inter_of_mem_of_mem ainl₁ ainl₂)

theorem mem_inter_iff (a : A) (s₁ s₂ : finset A) : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
iff.intro
 (λ h, and.intro (mem_of_mem_inter_left h) (mem_of_mem_inter_right h))
(λ h, mem_inter (and.elim_left h) (and.elim_right h))


theorem mem_inter_eq (a : A) (s₁ s₂ : finset A) : (a ∈ s₁ ∩ s₂) = (a ∈ s₁ ∧ a ∈ s₂) :=
propext (mem_inter_iff _ _ _)

theorem inter_comm (s₁ s₂ : finset A) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
ext (λ a, by repeat {rw mem_inter_eq}; exact and.comm)


theorem inter_assoc (s₁ s₂ s₃ : finset A) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
ext (λ a, by repeat {rw mem_inter_eq}; exact and.assoc)

theorem inter_left_comm (s₁ s₂ s₃ : finset A) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
left_comm _ inter_comm inter_assoc s₁ s₂ s₃

theorem inter_right_comm (s₁ s₂ s₃ : finset A) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
right_comm _ inter_comm inter_assoc s₁ s₂ s₃


theorem inter_self (s : finset A) : s ∩ s = s :=
ext (λ a, iff.intro
  (λ h, mem_of_mem_inter_right h)
  (λ h, mem_inter h h))

theorem inter_empty (s : finset A) : s ∩ empty = empty :=
ext (λ a, iff.intro
  (suppose a ∈ s ∩ empty, absurd (mem_of_mem_inter_right this) (not_mem_empty _))
  (assume h, absurd h (not_mem_empty _)))

theorem empty_inter (s : finset A) : empty ∩ s = empty :=
calc empty ∩ s = s ∩ empty : inter_comm _ _
       ... = empty     : inter_empty _

theorem singleton_inter_of_mem {a : A} {s : finset A} (H : a ∈ s) :
  insert a empty ∩ s = insert a empty :=
ext (take x,
  begin
    rewrite [mem_inter_eq, mem_singleton_iff],
    exact iff.intro
      (suppose x = a ∧ x ∈ s, and.left this)
      (suppose x = a, and.intro this (eq.subst (eq.symm this) H))
  end)

theorem singleton_inter_of_not_mem {a : A} {s : finset A} (H : a ∉ s) :
  insert a empty ∩ s = empty :=
ext (take x,
  begin
    rewrite [mem_inter_eq, mem_singleton_iff, mem_empty_eq],
    exact iff.intro
      (suppose x = a ∧ x ∈ s, H (eq.subst (and.left this) (and.right this)))
      (false.elim)
end)

end inter

/- distributivity laws -/
section inter
variable [h : decidable_eq A]
include h

theorem inter_distrib_left (s t u : finset A) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
ext (λ x, by rw [mem_inter_eq];repeat {rw mem_union_eq};repeat {rw mem_inter_eq}; super)

theorem inter_distrib_right (s t u : finset A) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
ext (take x, by rw [mem_inter_eq]; repeat {rw mem_union_eq}; repeat {rw mem_inter_eq}; super)

theorem union_distrib_left (s t u : finset A) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
ext (take x, by rw [mem_union_eq]; repeat {rw mem_inter_eq}; repeat {rw mem_union_eq}; super)

theorem union_distrib_right (s t u : finset A) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
ext (take x, by rw [mem_union_eq]; repeat {rw mem_inter_eq}; repeat {rw mem_union_eq}; super)

end inter

/- subset -/
definition subset (s₁ s₂ : finset A) : Prop :=
quot.lift_on₂ s₁ s₂
  (λ l₁ l₂, sublist l₁.1 l₂.1)
  (λ v₁ v₂ w₁ w₂ p₁ p₂, propext (iff.intro
    (λ s₁ a i, perm.mem_perm p₂ (s₁ (perm.mem_perm (perm.symm p₁) i)))
    (λ s₂ a i, perm.mem_perm (perm.symm p₂) (s₂ (perm.mem_perm p₁ i)))))

infix [priority finset.prio] ⊆ := subset

theorem empty_subset (s : finset A) : empty ⊆ s :=
quot.induction_on s (λ l, list.nil_subset l.1)

-- theorem subset_univ [h : fintype A] (s : finset A) : s ⊆ univ :=
-- quot.induction_on s (λ l a i, fintype.complete a)

theorem subset.refl (s : finset A) : s ⊆ s :=
quot.induction_on s (λ l, list.subset.refl l.1)

theorem subset.trans {s₁ s₂ s₃ : finset A} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
quot.induction_on₃ s₁ s₂ s₃ (λ l₁ l₂ l₃ h₁ h₂, list.subset.trans h₁ h₂)

theorem mem_of_subset_of_mem {s₁ s₂ : finset A} {a : A} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ h₁ h₂, h₁ h₂)

theorem subset.antisymm {s₁ s₂ : finset A} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
ext (take x, iff.intro (assume H, mem_of_subset_of_mem H₁ H) (assume H, mem_of_subset_of_mem H₂ H))


-- alternative name
theorem eq_of_subset_of_subset {s₁ s₂ : finset A} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
subset.antisymm H₁ H₂

theorem subset_of_forall {s₁ s₂ : finset A} : (∀x, x ∈ s₁ → x ∈ s₂) → s₁ ⊆ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ H, H)

theorem subset_insert [h : decidable_eq A] (s : finset A) (a : A) : s ⊆ insert a s :=
subset_of_forall (take x, suppose x ∈ s, mem_insert_of_mem _ this)

theorem eq_empty_of_subset_empty {x : finset A} (H : x ⊆ empty) : x = empty :=
subset.antisymm H (empty_subset x)

theorem subset_empty_iff (x : finset A) : x ⊆ empty ↔ x = empty :=
iff.intro eq_empty_of_subset_empty (take xeq, by rewrite xeq; apply subset.refl empty)

section
variable [decA : decidable_eq A]
include decA

theorem erase_subset_erase (a : A) {s t : finset A} (H : s ⊆ t) : erase a s ⊆ erase a t :=
begin
  apply subset_of_forall,
  intro x,
  repeat {rw mem_erase_eq},
  intro H',
  show x ∈ t ∧ x ≠ a, from and.intro (mem_of_subset_of_mem H (and.left H')) (and.right H')
end

theorem erase_subset  (a : A) (s : finset A) : erase a s ⊆ s :=
begin
  apply subset_of_forall,
  intro x,
  rewrite mem_erase_eq,
  intro H,
  apply and.left H
end

theorem erase_eq_of_not_mem {a : A} {s : finset A} (anins : a ∉ s) : erase a s = s :=
eq_of_subset_of_subset (erase_subset _ _)
  (subset_of_forall (take x, assume xs : x ∈ s,
    have x ≠ a, from assume H', anins (eq.subst H' xs),
mem_erase_of_ne_of_mem this xs))


theorem erase_insert_subset (a : A) (s : finset A) : erase a (insert a s) ⊆ s :=
decidable.by_cases
  (assume ains : a ∈ s, by rewrite [insert_eq_of_mem ains]; apply erase_subset)
  (assume nains : a ∉ s, by rewrite [erase_insert nains]; apply subset.refl)

theorem erase_subset_of_subset_insert {a : A} {s t : finset A} (H : s ⊆ insert a t) :
  erase a s ⊆ t :=
subset.trans (erase_subset_erase _ H) (erase_insert_subset _ _)


theorem insert_erase_subset (a : A) (s : finset A) : s ⊆ insert a (erase a s) :=
decidable.by_cases
  (assume ains : a ∈ s, by rewrite [insert_erase ains]; apply subset.refl)
  (assume nains : a ∉ s, by rewrite[erase_eq_of_not_mem nains]; apply subset_insert)

theorem insert_subset_insert (a : A) {s t : finset A} (H : s ⊆ t) : insert a s ⊆ insert a t :=
begin
  apply subset_of_forall,
  intro x,
  repeat {rw mem_insert_eq},
  intro H',
  cases H' with xeqa xins,
    exact (or.inl xeqa),
  exact (or.inr (mem_of_subset_of_mem H xins))
end

theorem subset_insert_of_erase_subset {s t : finset A} {a : A} (H : erase a s ⊆ t) :
  s ⊆ insert a t :=
subset.trans (insert_erase_subset a s) (insert_subset_insert _ H)

theorem subset_insert_iff (s t : finset A) (a : A) : s ⊆ insert a t ↔ erase a s ⊆ t :=
iff.intro erase_subset_of_subset_insert subset_insert_of_erase_subset

end


/- upto -/
section upto

definition upto (n : nat) : finset nat :=
to_finset_of_nodup (list.upto n) (nodup_upto n)

theorem card_upto : ∀ n, card (upto n) = n :=
list.length_upto

theorem lt_of_mem_upto {n a : nat} : a ∈ upto n → a < n :=
@list.lt_of_mem_upto n a

theorem mem_upto_succ_of_mem_upto {n a : nat} : a ∈ upto n → a ∈ upto (succ n) :=
list.mem_upto_succ_of_mem_upto

theorem mem_upto_of_lt {n a : nat} : a < n → a ∈ upto n :=
@list.mem_upto_of_lt n a

theorem mem_upto_iff (a n : nat) : a ∈ upto n ↔ a < n :=
iff.intro lt_of_mem_upto mem_upto_of_lt

theorem mem_upto_eq (a n : nat) : a ∈ upto n = (a < n) :=
propext (mem_upto_iff _ _)

end upto

theorem upto_zero : upto 0 = empty := rfl

theorem upto_succ (n : ℕ) : upto (succ n) = upto n ∪ (insert n empty) :=
begin
  apply ext, intro x,
  rw [mem_union_iff], repeat {rw mem_upto_iff}, simp [mem_singleton_iff, nat.le_iff_lt_or_eq, lt_succ_iff_le] 
end

/- useful rules for calculations with quantifiers -/
theorem exists_mem_empty_iff {A : Type} (P : A → Prop) : (∃ x, mem x empty ∧ P x) ↔ false :=
iff.intro
  (assume H,
    let ⟨x,H1⟩ := H in
    not_mem_empty _ (H1^.left))
  (assume H, false.elim H)

theorem exists_mem_empty_eq {A : Type} (P : A → Prop) : (∃ x, mem x empty ∧ P x) = false :=
propext (exists_mem_empty_iff _)

theorem exists_mem_insert_iff {A : Type} [d : decidable_eq A]
    (a : A) (s : finset A) (P : A → Prop) :
  (∃ x, x ∈ insert a s ∧ P x) ↔ P a ∨ (∃ x, x ∈ s ∧ P x) :=
iff.intro
  (assume H,
    let ⟨x,H1,H2⟩ := H in
    or.elim (eq_or_mem_of_mem_insert H1)
      (suppose x = a, or.inl (eq.subst this H2))
      (suppose x ∈ s, or.inr (exists.intro x (and.intro this H2))))
  (assume H,
    or.elim H
      (suppose P a, exists.intro a (and.intro (mem_insert _ _) this))
      (suppose ∃ x, x ∈ s ∧ P x,
        let ⟨x,H2,H3⟩ := this in
        exists.intro x (and.intro (mem_insert_of_mem _ H2) H3)))


theorem exists_mem_insert_eq {A : Type} [d : decidable_eq A] (a : A) (s : finset A) (P : A → Prop) :
  (∃ x, x ∈ insert a s ∧ P x) = (P a ∨ (∃ x, x ∈ s ∧ P x)) :=
propext (exists_mem_insert_iff _ _ _)

theorem forall_mem_empty_iff {A : Type} (P : A → Prop) : (∀ x, mem x empty → P x) ↔ true :=
iff.intro
  (assume H, trivial)
(assume H, take x, assume H', absurd H' (not_mem_empty _))


theorem forall_mem_empty_eq {A : Type} (P : A → Prop) : (∀ x, mem x empty → P x) = true :=
propext (forall_mem_empty_iff _)

theorem forall_mem_insert_iff {A : Type} [d : decidable_eq A]
    (a : A) (s : finset A) (P : A → Prop) :
  (∀ x, x ∈ insert a s → P x) ↔ P a ∧ (∀ x, x ∈ s → P x) :=
iff.intro
  (assume H, and.intro (H _ (mem_insert _ _)) (take x, assume H', H _ (mem_insert_of_mem _ H')))
  (assume H, take x, assume H' : x ∈ insert a s,
    or.elim (eq_or_mem_of_mem_insert H')
      (suppose x = a, eq.subst (eq.symm this) (and.left H))
(suppose x ∈ s, and.right H _ this))

theorem forall_mem_insert_eq {A : Type} [d : decidable_eq A] (a : A) (s : finset A) (P : A → Prop) :
  (∀ x, x ∈ insert a s → P x) = (P a ∧ (∀ x, x ∈ s → P x)) :=
propext (forall_mem_insert_iff _ _ _)

end finset
