import .basic
open list quot subtype decidable function

namespace finset
/- image (corresponds to map on list) -/
section image
variables {A B : Type}
variable [h : decidable_eq B]
include h

definition image (f : A → B) (s : finset A) : finset B :=
quot.lift_on s
  (λ l, to_finset (list.map f l.1))
  (λ l₁ l₂ p, quot.sound (perm.perm_erase_dup_of_perm (perm.perm_map _ p)))


infix `'` := image

theorem image_empty (f : A → B) : image f empty = empty := rfl

theorem mem_image_of_mem (f : A → B) {s : finset A} {a : A} : a ∈ s → f a ∈ image f s :=
quot.induction_on s (take l, assume H : a ∈ l.1, mem_to_finset (mem_map f H))

theorem mem_image {f : A → B} {s : finset A} {a : A} {b : B}
    (H1 : a ∈ s) (H2 : f a = b) :
  b ∈ image f s :=
eq.subst H2 (mem_image_of_mem f H1)

theorem exists_of_mem_image {f : A → B} {s : finset A} {b : B} :
  b ∈ image f s → ∃a, a ∈ s ∧ f a = b :=
quot.induction_on s
  (take l, assume H : b ∈ erase_dup (list.map f l.1),
    exists_of_mem_map (mem_of_mem_erase_dup H))


theorem mem_image_iff (f : A → B) {s : finset A} {y : B} : y ∈ image f s ↔ ∃x, x ∈ s ∧ f x = y :=
iff.intro exists_of_mem_image
  (assume H, let ⟨x,H₁,H₂⟩ := H in mem_image H₁ H₂)

theorem mem_image_eq (f : A → B) {s : finset A} {y : B} : y ∈ image f s = ∃x, x ∈ s ∧ f x = y :=
propext (mem_image_iff f)

theorem mem_image_of_mem_image_of_subset {f : A → B} {s t : finset A} {y : B}
    (H1 : y ∈ image f s) (H2 : s ⊆ t) : y ∈ image f t :=
let ⟨x, H3, H4⟩ := exists_of_mem_image H1 in
have H5 : x ∈ t, from mem_of_subset_of_mem H2 H3,
show y ∈ image f t, from mem_image H5 H4

theorem image_insert [h' : decidable_eq A] (f : A → B) (s : finset A) (a : A) :
  image f (insert a s) = insert (f a) (image f s) :=
ext (take y, iff.intro
  (assume H : y ∈ image f (insert a s),
    let ⟨x,H1l,H1r⟩ := exists_of_mem_image H in
    have x = a ∨ x ∈ s, from eq_or_mem_of_mem_insert H1l,
    or.elim this
      (suppose x = a,
        have f a = y, from eq.subst this H1r,
        show y ∈ insert (f a) (image f s), from eq.subst this (mem_insert _ _))
      (suppose x ∈ s,
        have f x ∈ image f s, from mem_image_of_mem f this,
        show y ∈ insert (f a) (image f s), from eq.subst H1r (mem_insert_of_mem _ this)))
  (suppose y ∈ insert (f a) (image f s),
    have y = f a ∨ y ∈ image f s, from eq_or_mem_of_mem_insert this,
    or.elim this
      (assume eq : y = f a,
        have f a ∈ image f (insert a s), from mem_image_of_mem f (mem_insert _ _),
        show y ∈ image f (insert a s), by rw eq;exact this)
      (suppose y ∈ image f s,
        show y ∈ image f (insert a s), from mem_image_of_mem_image_of_subset this (subset_insert _ _) )))


lemma image_comp {C : Type} [deceqC : decidable_eq C] {f : B → C} {g : A → B} {s : finset A} :
  image (f∘g) s = image f (image g s) :=
ext (take z, iff.intro
  (suppose z ∈ image (f∘g) s,
   let ⟨x,Hx,Hgfx⟩ := exists_of_mem_image this in
    by rewrite -Hgfx; apply mem_image_of_mem _ (mem_image_of_mem _ Hx))
  (suppose z ∈ image f (image g s),
   let ⟨y,Hy,Hfy⟩ := exists_of_mem_image this in
   let ⟨x,Hx,Hgx⟩ := exists_of_mem_image Hy in
   mem_image Hx (begin simp [comp, Hgx, Hfy] end)))

lemma image_subset {a b : finset A} (f : A → B) (H : a ⊆ b) : image f a ⊆ image f b :=
subset_of_forall
  (take y, assume Hy : y ∈ image f a,
    let ⟨x,Hx₁,Hx₂⟩ := exists_of_mem_image Hy in
    mem_image (mem_of_subset_of_mem H Hx₁) Hx₂)

theorem image_union [h' : decidable_eq A] (f : A → B) (s t : finset A) :
  image f (s ∪ t) = image f s ∪ image f t :=
ext (take y, iff.intro
  (assume H : y ∈ image f (s ∪ t),
   let ⟨x,xst,fxy⟩ := exists_of_mem_image H in
    or.elim (mem_or_mem_of_mem_union xst)
      (assume xs, mem_union_l (mem_image xs fxy))
      (assume xt, mem_union_r (mem_image xt fxy)))
  (assume H : y ∈ image f s ∪ image f t,
    or.elim (mem_or_mem_of_mem_union H)
      (assume yifs : y ∈ image f s,
        let ⟨x,xs,fxy⟩ := exists_of_mem_image yifs in
        mem_image (mem_union_l xs) fxy)
      (assume yift : y ∈ image f t,
        let ⟨x,xt,fxy⟩ := exists_of_mem_image yift in
        mem_image (mem_union_r xt) fxy)))

end image


/- separation and set-builder notation -/
section sep
variables {A : Type} [deceq : decidable_eq A]
include deceq
variables (p : A → Prop) [decp : decidable_pred p] (s : finset A) {x : A}
include decp

definition sep : finset A :=
quot.lift_on s
  (λl, to_finset_of_nodup
    (list.filter p l.1)
    (list.nodup_filter p l.2))
(λ l₁ l₂ u, quot.sound (perm.perm_filter u))

-- notation [priority finset.prio] `{` binder ` ∈ ` s ` | ` r:(scoped:1 p, sep p s) `}` := r

theorem sep_empty : sep p empty = empty := rfl

variables {p s}

theorem of_mem_sep : x ∈ sep p s → p x :=
quot.induction_on s (take l, list.of_mem_filter)

theorem mem_of_mem_sep : x ∈ sep p s → x ∈ s :=
quot.induction_on s (take l, list.mem_of_mem_filter)

theorem mem_sep_of_mem {x : A} : x ∈ s → p x → x ∈ sep p s :=
quot.induction_on s (take l, list.mem_filter_of_mem)

variables (p s)


theorem mem_sep_iff : x ∈ sep p s ↔ x ∈ s ∧ p x :=
iff.intro
  (assume H, and.intro (mem_of_mem_sep H) (of_mem_sep H))
  (assume H, mem_sep_of_mem (and.left H) (and.right H))

theorem mem_sep_eq : x ∈ sep p s = (x ∈ s ∧ p x) :=
propext (mem_sep_iff _ _)

variable t : finset A

theorem mem_sep_union_iff : x ∈ sep p (s ∪ t) ↔ x ∈ sep p s ∨ x ∈ sep p t :=
by repeat {rw mem_sep_iff}; rw [mem_union_iff]; super

end sep


section

variables {A : Type} [deceqA : decidable_eq A]
include deceqA

theorem eq_sep_of_subset {s t : finset A} (ssubt : s ⊆ t) : s = sep (λ x, x ∈ s) t := 
ext (take x, iff.intro
  (suppose x ∈ s, mem_sep_of_mem (mem_of_subset_of_mem ssubt this) this)
  (suppose x ∈ sep (λ x, x ∈ s) t, @of_mem_sep _ _ _ _ _ _ this))

end

/- set difference -/
section diff
variables {A : Type} [deceq : decidable_eq A]
include deceq

definition diff (s t : finset A) : finset A := sep (λ x, x ∉ t) s
infix ` \ ` := diff

theorem mem_of_mem_diff {s t : finset A} {x : A} (H : x ∈ s \ t) : x ∈ s :=
mem_of_mem_sep H

theorem not_mem_of_mem_diff {s t : finset A} {x : A} (H : x ∈ s \ t) : x ∉ t :=
@of_mem_sep _ _ _ _ _ _ H

theorem mem_diff {s t : finset A} {x : A} (H1 : x ∈ s) (H2 : x ∉ t) : x ∈ s \ t :=
mem_sep_of_mem H1 H2

theorem mem_diff_iff (s t : finset A) (x : A) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
iff.intro
  (assume H, and.intro (mem_of_mem_diff H) (not_mem_of_mem_diff H))
  (assume H, mem_diff (and.left H) (and.right H))

theorem mem_diff_eq (s t : finset A) (x : A) : x ∈ s \ t = (x ∈ s ∧ x ∉ t) :=
propext (mem_diff_iff _ _ _)

theorem union_diff_cancel {s t : finset A} (H : s ⊆ t) : s ∪ (t \ s) = t :=
ext (take x, iff.intro
  (suppose x ∈ s ∪ (t \ s),
    or.elim (mem_or_mem_of_mem_union this)
      (suppose x ∈ s, mem_of_subset_of_mem H this)
      (suppose x ∈ t \ s, mem_of_mem_diff this))
  (assume h,
    decidable.by_cases
      (suppose x ∈ s, mem_union_left _ this)
      (suppose x ∉ s, mem_union_right _ (mem_diff h this))))

theorem diff_union_cancel {s t : finset A} (H : s ⊆ t) : (t \ s) ∪ s = t :=
@eq.subst _ (λ x, x = t) _ _ (union_comm _ _) (union_diff_cancel H)

end diff

/- set complement -/
section complement
-- TODO
end complement

end finset
