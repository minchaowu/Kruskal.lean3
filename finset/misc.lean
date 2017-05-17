open nat set

theorem lt_succ_iff_le (m n : nat) : m < succ n ↔ m ≤ n :=
iff.intro le_of_lt_succ lt_succ_of_le

theorem ext {X : Type} {a b : set X} (H : ∀x, x ∈ a ↔ x ∈ b) : a = b :=
funext (take x, propext (H x))

theorem not_mem_empty {X : Type} (x : X) : ¬ (x ∈ (∅ : set X)) :=
assume H : x ∈ ∅, H

section 
/- universal set -/
variable {α : Type}

theorem mem_univ (x : α) : x ∈ @univ α := trivial

theorem mem_univ_iff (x : α) : x ∈ @univ α ↔ true := iff.rfl

@[simp]
theorem mem_univ_eq (x : α) : x ∈ @univ α = true := rfl

theorem empty_ne_univ [h : inhabited α] : (∅ : set α) ≠ univ :=
assume H : ∅ = univ,
absurd (mem_univ (inhabited.default α)) (eq.rec_on H (not_mem_empty _))

@[simp]
theorem subset_univ (s : set α) : s ⊆ univ := λ x H, trivial

end


theorem eq_sep_of_subset {X : Type} {s t : set X} (ssubt : s ⊆ t) : s = {x ∈ t | x ∈ s} :=
ext (take x, iff.intro
  (suppose x ∈ s, and.intro (ssubt this) this)
(suppose x ∈ {x ∈ t | x ∈ s}, and.right this))

theorem subset_insert {X : Type} (x : X) (a : set X) : a ⊆ insert x a :=
take y, assume ys, or.inr ys

theorem not_mem_of_mem_diff {A : Type} {s t : set A} {x : A} (H : x ∈ s \ t) : x ∉ t :=
and.right H

theorem mem_insert {X : Type} (x : X) (s : set X) : x ∈ insert x s :=
or.inl rfl

theorem mem_singleton {X : Type} (a : X) : a ∈ insert a (∅ : set X) := mem_insert _ _

theorem eq_of_mem_singleton {X : Type} {x y : X} (h : x ∈ insert y (∅ : set X)) : x = y :=
or.elim (h)
  (suppose x = y, this)
(suppose x ∈ ∅, absurd this (not_mem_empty _))

theorem mem_singleton_iff {X : Type} (a b : X) : a ∈ insert b (∅ : set X) ↔ a = b :=
iff.intro
  (assume ainb, or.elim ainb (λ aeqb, aeqb) (λ f, false.elim f))
(assume aeqb, or.inl aeqb)

theorem eq_empty_of_forall_not_mem {X : Type} {s : set X} (H : ∀ x, x ∉ s) : s = ∅ :=
ext (take x, iff.intro
  (assume xs, absurd xs (H x))
(assume xe, absurd xe (not_mem_empty _)))

section
  open classical
  variable {X : Type}

  theorem exists_mem_of_ne_empty {s : set X} (H : s ≠ ∅) : ∃ x, x ∈ s :=
  by_contradiction (assume H', H (eq_empty_of_forall_not_mem (forall_not_of_not_exists H')))

end

definition eq_on {X Y : Type} (f1 f2 : X → Y) (a : set X) : Prop :=
∀ x ∈ a, f1 x = f2 x

attribute [reducible]
definition maps_to {X Y : Type} (f : X → Y) (a : set X) (b : set Y) : Prop := ∀⦃x⦄, x ∈ a → f x ∈ b


attribute [reducible]
definition surj_on {X Y : Type} (f : X → Y) (a : set X) (b : set Y) : Prop := b ⊆ image f a

attribute [reducible]
definition inj_on {X Y: Type} (f : X → Y) (a : set X) : Prop :=
∀⦃x1 x2 : X⦄, x1 ∈ a → x2 ∈ a → f x1 = f x2 → x1 = x2

section function

variables {X Y Z: Type}
/- left inverse -/

-- g is a left inverse to f on a
attribute [reducible]
definition left_inv_on  (g : Y → X) (f : X → Y) (a : set X) : Prop :=
∀ x ∈ a, g (f x) = x

theorem left_inv_on_of_eq_on_left {g1 g2 : Y → X} {f : X → Y} {a : set X} {b : set Y}
  (fab : maps_to f a b) (eqg : eq_on g1 g2 b) (H : left_inv_on g1 f a) : left_inv_on g2 f a :=
take x,
assume xa : x ∈ a,
calc
  g2 (f x) = g1 (f x) : eq.symm (eqg _ (fab xa))
  ... = x : H _ xa

theorem left_inv_on_of_eq_on_right {g : Y → X} {f1 f2 : X → Y} {a : set X}
  (eqf : eq_on f1 f2 a) (H : left_inv_on g f1 a) : left_inv_on g f2 a :=
take x,
assume xa : x ∈ a,
calc
  g (f2 x) = g (f1 x) : by rw eq.symm (eqf _ xa)
... = x : H _ xa

theorem inj_on_of_left_inv_on {g : Y → X} {f : X → Y} {a : set X} (H : left_inv_on g f a) :
  inj_on f a :=
take x1 x2,
assume x1a : x1 ∈ a,
assume x2a : x2 ∈ a,
assume H1 : f x1 = f x2,
calc
  x1     = g (f x1) : eq.symm (H _ x1a)
     ... = g (f x2) : by rw H1
     ... = x2 : H _ x2a

theorem left_inv_on_comp {f' : Y → X} {g' : Z → Y} {g : Y → Z} {f : X → Y}
   {a : set X} {b : set Y} (fab : maps_to f a b)
    (Hf : left_inv_on f' f a) (Hg : left_inv_on g' g b) : left_inv_on (f' ∘ g') (g ∘ f) a :=
take x : X,
assume xa : x ∈ a,
have fxb : f x ∈ b, from fab xa,
calc
  f' (g' (g (f x))) = f' (f x) : by rw Hg _ fxb
  ... = x : Hf _ xa


/- right inverse -/

-- g is a right inverse to f on a
attribute [reducible]
definition right_inv_on (g : Y → X) (f : X → Y) (b : set Y) : Prop :=
left_inv_on f g b

theorem right_inv_on_of_eq_on_left {g1 g2 : Y → X} {f : X → Y} {a : set X} {b : set Y}
  (eqg : eq_on g1 g2 b) (H : right_inv_on g1 f b) : right_inv_on g2 f b :=
left_inv_on_of_eq_on_right eqg H

theorem right_inv_on_of_eq_on_right {g : Y → X} {f1 f2 : X → Y} {a : set X} {b : set Y}
  (gba : maps_to g b a) (eqf : eq_on f1 f2 a) (H : right_inv_on g f1 b) : right_inv_on g f2 b :=
left_inv_on_of_eq_on_left gba eqf H

theorem surj_on_of_right_inv_on {g : Y → X} {f : X → Y} {a : set X} {b : set Y}
    (gba : maps_to g b a) (H : right_inv_on g f b) :
  surj_on f a b :=
take y,
assume yb : y ∈ b,
have gya : g y ∈ a, from gba yb,
have H1 : f (g y) = y, from H _ yb,
exists.intro (g y) (and.intro gya H1)


end function

section

-- classical inverse

open classical
variables {X Y : Type}

noncomputable instance dec_prop (p : Prop) : decidable p := prop_decidable p

noncomputable definition inv_fun (f : X → Y) (a : set X) (dflt : X) (y : Y) : X :=
if H : ∃ x ∈ a, f x = y then some H else dflt

theorem inv_fun_pos {f : X → Y} {a : set X} {dflt : X} {y : Y}
  (H : ∃ x ∈ a, f x = y) : (inv_fun f a dflt y ∈ a) ∧ (f (inv_fun f a dflt y) = y) :=
have H1 : inv_fun f a dflt y = some H, from dif_pos H,
let ⟨x,ina⟩ := some_spec H in
⟨by rw H1; assumption,by rw H1; assumption⟩

theorem inv_fun_neg {f : X → Y} {a : set X} {dflt : X} {y : Y}
  (H : ¬ ∃ x ∈ a, f x = y) : inv_fun f a dflt y = dflt :=
dif_neg H

variables {f : X → Y} {a : set X} {b : set Y}

theorem maps_to_inv_fun {dflt : X} (dflta : dflt ∈ a) :
  maps_to (inv_fun f a dflt) b a :=
let f' := inv_fun f a dflt in
take y,
assume yb : y ∈ b,
show f' y ∈ a, from
  by_cases
    (assume H : ∃ x ∈ a, f x = y,
      and.left (inv_fun_pos H))
    (assume H : ¬ ∃ x ∈ a, f x = y,
begin dsimp, rw (inv_fun_neg H), assumption end)

theorem left_inv_on_inv_fun_of_inj_on (dflt : X) (H : inj_on f a) :
  left_inv_on (inv_fun f a dflt) f a :=
let f' := inv_fun f a dflt in
take x,
assume xa : x ∈ a,
have H1 : ∃ x' ∈ a, f x' = f x, from ⟨x,xa,rfl⟩,
have H2 : f' (f x) ∈ a ∧ f (f' (f x)) = f x, from inv_fun_pos H1,
show f' (f x) = x, from H (and.left H2) xa (and.right H2)

theorem surj_on_inv_fun_of_inj_on (dflt : X) (mapsto : maps_to f a b) (H : inj_on f a) :
  surj_on (inv_fun f a dflt) b a :=
surj_on_of_right_inv_on mapsto (left_inv_on_inv_fun_of_inj_on dflt H)


end
