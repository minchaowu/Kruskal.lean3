import .finset.to_set

open nat classical

variable {A : Type}

noncomputable instance type_decidable_eq (A : Type) : decidable_eq A :=
λ a b, prop_decidable (a = b)

namespace set

attribute [class]
definition finite (s : set A) : Prop := ∃ (s' : finset A), s = finset.to_set s'

attribute [instance]
definition finite_finset (s : finset A) : finite (finset.to_set s) :=
exists.intro s rfl

noncomputable instance dec_finite (s : set A) : decidable (finite s) := prop_decidable (finite s)

noncomputable definition to_finset (s : set A) : finset A :=
if fins : finite s then some fins else finset.empty

theorem to_finset_of_not_finite {s : set A} (nfins : ¬ finite s) : to_finset s = finset.empty := 
dif_neg nfins

theorem to_set_to_finset (s : set A) [fins : finite s] : finset.to_set (to_finset s) = s :=
have to_finset s = some fins, from dif_pos fins,
by rw this; exact eq.symm (some_spec fins)

theorem mem_to_finset_eq (a : A) (s : set A) [finite s] :
  (finset.mem a (to_finset s)) = (a ∈ s) :=
have (finset.mem a (to_finset s)) = (a ∈ (finset.to_set (to_finset s))), from rfl,
begin rw this, rw [to_set_to_finset] end

theorem to_set_to_finset_of_not_finite {s : set A} (nfins : ¬ finite s) :
  finset.to_set (to_finset s) = ∅ :=
have to_finset s = finset.empty, from to_finset_of_not_finite nfins,
begin rw this, reflexivity end

theorem to_finset_to_set (s : finset A) : to_finset (finset.to_set s) = s :=
begin rw finset.eq_eq_to_set_eq, rw to_set_to_finset end

theorem to_finset_eq_of_to_set_eq {s : set A} {t : finset A} (H : finset.to_set t = s) :
  to_finset s = t :=
finset.eq_of_to_set_eq_to_set (begin rw -H, rw to_finset_to_set end)

theorem finite_of_to_set_to_finset_eq {s : set A} (H : finset.to_set (to_finset s) = s) :
  finite s :=
by rewrite -H; apply finite_finset

attribute [instance]
theorem finite_empty : finite (∅ : set A) :=
by rewrite [-finset.to_set_empty]; apply finite_finset

theorem to_finset_empty : to_finset (∅ : set A) = finset.empty :=
to_finset_eq_of_to_set_eq finset.to_set_empty

theorem to_finset_eq_empty_of_eq_empty {s : set A} [fins : finite s] (H : s = ∅) :
  to_finset s = finset.empty := by rewrite [H, to_finset_empty]

theorem eq_empty_of_to_finset_eq_empty {s : set A} [fins : finite s]
    (H : to_finset s = finset.empty) :
s = ∅ := by rewrite [-finset.to_set_empty, -H, to_set_to_finset]

theorem to_finset_eq_empty (s : set A) [fins : finite s] :
  (to_finset s = finset.empty) ↔ (s = ∅) :=
iff.intro eq_empty_of_to_finset_eq_empty to_finset_eq_empty_of_eq_empty

attribute [instance]
theorem finite_insert (a : A) (s : set A) [finite s] : finite (set.insert a s) :=
exists.intro (finset.insert a (to_finset s))
(by rw [-(to_set_to_finset s), finset.to_set_insert, to_finset_to_set])

theorem to_finset_insert (a : A) (s : set A) [finite s] :
  to_finset (insert a s) = finset.insert a (to_finset s) :=
begin apply to_finset_eq_of_to_set_eq, 
rw [-finset.to_set_insert, to_set_to_finset], reflexivity end

attribute [instance]
theorem finite_union (s t : set A) [finite s] [finite t] :
  finite (s ∪ t) :=
exists.intro (to_finset s ∪ to_finset t)
(by rewrite [finset.to_set_union]; repeat {rw to_set_to_finset})

theorem to_finset_union (s t : set A) [finite s] [finite t] :
  to_finset (s ∪ t) = (to_finset s ∪ to_finset t) :=
by apply to_finset_eq_of_to_set_eq; rw [finset.to_set_union]; repeat {rw to_set_to_finset}

attribute [instance]
theorem finite_inter (s t : set A) [finite s] [finite t] :
  finite (s ∩ t) :=
exists.intro (to_finset s ∩ to_finset t)
(by rw [finset.to_set_inter]; repeat {rw to_set_to_finset})

theorem to_finset_inter (s t : set A) [finite s] [finite t] :
  to_finset (s ∩ t) = (to_finset s ∩ to_finset t) :=
by apply to_finset_eq_of_to_set_eq; rw [finset.to_set_inter]; repeat {rw to_set_to_finset}

noncomputable instance dec_prop (p : Prop) : decidable p := prop_decidable p

attribute [instance]
theorem finite_sep (s : set A) (p : A → Prop) [finite s] :
  finite {x ∈ s | p x}  :=
exists.intro (finset.sep p (to_finset s))
(by rw [finset.to_set_sep]; rw to_set_to_finset; reflexivity)

theorem to_finset_sep (s : set A) (p : A → Prop) [finite s] :
  to_finset {x ∈ s | p x} = finset.sep p (to_finset s) :=
begin apply to_finset_eq_of_to_set_eq; rewrite [finset.to_set_sep, to_set_to_finset], reflexivity end

attribute [instance]
theorem finite_image {B : Type} (f : A → B) (s : set A) [finite s] :
  finite (image f s) :=
exists.intro (finset.image f (to_finset s))
(begin rw [finset.to_set_image]; repeat {rw to_set_to_finset} end)

theorem to_finset_image {B : Type}  (f : A → B) (s : set A)
    [fins : finite s] :
  to_finset (image f s) = (finset.image f (to_finset s)) :=
by apply to_finset_eq_of_to_set_eq; rewrite [finset.to_set_image, to_set_to_finset]

attribute [instance]
theorem finite_diff (s t : set A) [finite s] : finite (s \ t) :=
finite_sep _ _

theorem to_finset_diff (s t : set A) [finite s] [finite t] :
        to_finset (s \ t) = (to_finset s \ to_finset t) :=
by apply to_finset_eq_of_to_set_eq; rw [finset.to_set_diff]; repeat {rw to_set_to_finset}

theorem finite_subset {s t : set A} [finite t] (ssubt : s ⊆ t) : finite s :=
by rewrite (eq_sep_of_subset ssubt); apply finite_sep

theorem to_finset_subset_to_finset_eq (s t : set A) [finite s] [finite t] :
  (to_finset s ⊆ to_finset t) = (s ⊆ t) :=
by rw [finset.subset_eq_to_set_subset]; repeat {rw to_set_to_finset}

theorem finite_of_finite_insert {s : set A} {a : A} (finias : finite (insert a s)) : finite s :=
finite_subset (subset_insert a s)

attribute [instance]
theorem finite_upto (n : ℕ) : finite {i | i < n} :=
by rewrite [-finset.to_set_upto n]; apply finite_finset

theorem to_finset_upto (n : ℕ) : to_finset {i | i < n} = finset.upto n :=
by apply (to_finset_eq_of_to_set_eq (finset.to_set_upto _))

theorem finite_of_surj_on {B : Type} {f : A → B} {s : set A} [finite s] {t : set B}
                          (H : surj_on f s t) :
        finite t :=
finite_subset H

theorem finite_of_inj_on {B : Type} {f : A → B} {s : set A} {t : set B} [finite t]
                         (mapsto : maps_to f s t) (injf : inj_on f s) :
        finite s :=
if H : s = ∅ then
  begin rewrite H; apply _, apply finite_empty end
else
  let ⟨dflt,xs⟩ := exists_mem_of_ne_empty H in
  let finv := inv_fun f s dflt in
  have surj_on finv t s, from surj_on_inv_fun_of_inj_on dflt mapsto injf,
  finite_of_surj_on this

-- theorem finite_of_bij_on {B : Type} {f : A → B} {s : set A} {t : set B} [finite s]
--                          (bijf : bij_on f s t) :
--         finite t :=
-- finite_of_surj_on (surj_on_of_bij_on bijf)

-- theorem finite_of_bij_on' {B : Type} {f : A → B} {s : set A} {t : set B} [finite t]
--                          (bijf : bij_on f s t) :
--         finite s :=
-- finite_of_inj_on (maps_to_of_bij_on bijf) (inj_on_of_bij_on bijf)

-- theorem finite_iff_finite_of_bij_on {B : Type} {f : A → B} {s : set A} {t : set B}
--                                     (bijf : bij_on f s t) :
--         finite s ↔ finite t :=
-- iff.intro (assume fs, finite_of_bij_on bijf) (assume ft, finite_of_bij_on' bijf)

-- theorem finite_powerset (s : set A) [finite s] : finite 𝒫 s :=
-- have H : 𝒫 s = finset.to_set ' (finset.to_set (#finset 𝒫 (to_finset s))),
--   from ext (take t, iff.intro
--     (suppose t ∈ 𝒫 s,
--       have t ⊆ s, from this,
--       have finite t, from finite_subset this,
--       have (#finset to_finset t ∈ 𝒫 (to_finset s)),
--         by rewrite [finset.mem_powerset_iff_subset, to_finset_subset_to_finset_eq]; apply `t ⊆ s`,
--       have to_finset t ∈ (finset.to_set (finset.powerset (to_finset s))), from this,
--       mem_image this (by rewrite to_set_to_finset))
--     (assume H',
--       obtain t' [(tmem : (#finset t' ∈ 𝒫 (to_finset s))) (teq : finset.to_set t' = t)],
--         from H',
--       show t ⊆ s,
--       begin
--         rewrite [-teq, finset.mem_powerset_iff_subset at tmem, -to_set_to_finset s],
--         rewrite -finset.subset_eq_to_set_subset, assumption
--      end)),
-- by rewrite H; apply finite_image


/- induction for finite sets -/

attribute [recursor 6]
theorem induction_finite {P : set A → Prop}
    (H1 : P ∅) (H2 : ∀ ⦃a : A⦄, ∀ {s : set A} [finite s], a ∉ s → P s → P (insert a s)) :
  ∀ (s : set A) [finite s], P s :=
(λ s fins, 
have ∀ s' : finset A, P (finset.to_set s'), from 
  λ s', @finset.induction_on _ _ (λ x, P (finset.to_set x)) s' 
  (by rw finset.to_set_empty; exact H1) 
  (begin 
    intros a s' anin ih, 
    rw [-finset.to_set_insert], apply H2, 
    {rw [-finset.mem_eq_mem_to_set], exact anin},
    {exact ih} 
   end),
begin rw [-to_set_to_finset s], exact (this (to_finset s)) end)

theorem induction_on_finite {P : set A → Prop} (s : set A) [finite s]
    (H1 : P ∅) (H2 : ∀ ⦃a : A⦄, ∀ {s : set A} [finite s], a ∉ s → P s → P (insert a s)) :
  P s :=
induction_finite H1 H2 s

end set
