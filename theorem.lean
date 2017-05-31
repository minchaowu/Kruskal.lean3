import .kruskal .higman data.list
open classical fin set nat subtype finite_tree kruskal function prod

noncomputable theory

theorem dne {p : Prop} (H : ¬¬p) : p := or.elim (em p) (assume Hp : p, Hp) (assume Hnp : ¬p, absurd Hnp H)

lemma tag_eq_of_eq {A : Type} {P : A → Prop} {a b : subtype P} (H : a = b) :a.1 = b.1 := by rewrite H

section

variables {A B : Type}
variable x : A × B

theorem prod_eta : (x.1,x.2) = x := prod.rec_on x (λ a b, rfl)

theorem eq_of_prod {A B : Type} {p q : A × B} (H1 : p.1 = q.1) (H2 : p.2 = q.2) : p = q :=
begin 
cases p with p1 p2,
dsimp at H1, dsimp at H2,
rw [H1,H2,prod_eta]
end

end

theorem ne_empty_of_image_on_univ {A B : Type} (f : A → B) [inhabited A] : image f univ ≠ ∅ :=
have (∅ : set A) ≠ univ, from empty_ne_univ,
have ∃ a, a ∈ (univ : set A), from exists_mem_of_ne_empty (ne.symm this),
let ⟨a,h⟩ := this in
have f a ∈ image f univ, from exists.intro a (and.intro h rfl),
set.ne_empty_of_mem this

theorem val_mapsto (n : ℕ) : maps_to fin.val (@univ (fin n)) {i : ℕ | i < n} :=
take x, assume Ha, is_lt x

theorem injective_val_on_univ (n : ℕ): inj_on fin.val (@univ (fin n)) :=
take x₁ x₂, assume H1, assume H2, assume eq, eq_of_veq eq

instance finite_univ_of_fin (n : ℕ) : finite (@univ (fin n)) :=
finite_of_inj_on (val_mapsto n) (injective_val_on_univ n)

theorem refl_of_image_on_univ {A B: Type} (f : A → B) : set.image f (@set.univ A) = {b : B | ∃ x, f x = b} :=
have Hl : set.image f (@set.univ A) ⊆ {b : B | ∃ x, f x = b}, from 
  take x, assume Hx, 
  let ⟨i,h⟩ := Hx in exists.intro i (and.right h),
have {b : B | ∃ x, f x = b} ⊆ set.image f  (@set.univ A), from 
  take x, assume Hx, 
  let ⟨i,h⟩ := Hx in exists.intro i (and.intro trivial h),
set.subset.antisymm Hl this

theorem finite_image_of_fin {A : Type} {n : ℕ} (f : fin n → A) : finite {a : A | ∃ x, f x = a} := 
have image f (@univ (fin n)) = {a : A | ∃ x, f x = a}, from refl_of_image_on_univ f,
have finite (image f (@univ (fin n))), from finite_image f (@univ (fin n)),
by super

-- need this to handle trees of the form (f n) where f : ℕ → finite_tree
theorem finite_tree_destruct {t : finite_tree} :
∃ n (ss : fin n → finite_tree), t = cons ss :=
finite_tree.cases_on t (λ n a, ⟨n,a,rfl⟩)

definition num_of_branches_at_root : finite_tree → ℕ
| (@cons n ts) := n

-- definition num_of_branches_at_root (t : finite_tree) (H : t ≠ node) : ℕ := 
-- some (exists_eq_cons_of_ne_node H)

-- definition branches_at_root : finite_tree → Π {n : ℕ}, fin n → finite_tree
-- | (@cons n ts) := ts
-- some (some_spec (exists_eq_cons_of_ne_node H))

-- definition set_of_branches' {n : ℕ} : finite_tree → set (finite_tree × ℕ)
-- | (@cons n ts) := {x : finite_tree × ℕ | ∃ a : fin n, ts a = x.1 ∧ val a = x.2}

-- {x : finite_tree × ℕ | ∃ a : fin n, ts a = x.1 ∧ val a = x.2}

def branches_aux {n : ℕ} (ts : fin n → finite_tree) : set (finite_tree × ℕ) := 
{x : finite_tree × ℕ | ∃ a : fin n, ts a = x.1 ∧ val a = x.2}

theorem empty_branches (ts : fin 0 → finite_tree) : branches_aux ts = ∅ :=
have ∀ x, x ∉ branches_aux ts, from λ x h, let ⟨a,ha⟩ := h in fin_zero_absurd a,
set.eq_empty_of_forall_not_mem this

definition branches : finite_tree → set (finite_tree × ℕ) 
| (@cons n ts) := branches_aux ts

theorem embeds_of_branches {t : finite_tree × ℕ} {T : finite_tree} : t ∈ (branches T) → t.1 ≼ T := 
begin
cases T with n ts,
intro H, cases H with a h,
cases t.1 with t1a t1s,
dsimp [embeds],apply or.inl,
fapply exists.intro,
exact a, rw h^.left, apply embeds_refl
end

theorem lt_of_size_of_branches {t : finite_tree × ℕ} {T : finite_tree} : t ∈ branches T → size t.1 < size T :=
begin 
cases T with n ts,
intro h,
assert h' : ∃ i, ts i = t.1, cases h with b hb, 
  {exact exists.intro b hb^.left},
cases h' with c hc, rw -hc, apply lt_of_size_branches_aux
end

theorem finite_set_of_branches {n : ℕ} (ts : fin n → finite_tree) : finite (branches_aux ts) := 
let f (a : fin n) : finite_tree × ℕ := (ts a, val a) in
let S : set (finite_tree × ℕ) := {x : finite_tree × ℕ | ∃ a : fin n, f a = x} in
have finS : finite S, from finite_image_of_fin f,
have H1 : S ⊆ branches_aux ts, from 
  λ x ⟨a,h⟩, ⟨a,⟨by rw -h,by rw -h⟩⟩,
have H2 : branches_aux ts ⊆ S, from 
  λ x ⟨a,h⟩, ⟨a,begin dsimp,rw [h^.left, h^.right], apply prod_eta end⟩, 
begin rw -(subset.antisymm H1 H2), exact finS end

theorem finite_branches (t : finite_tree) : finite (branches t) := 
by induction t; apply finite_set_of_branches

#check @minimal_bad_seq

section
parameter H : ∃ f, ¬ is_good f embeds

definition mbs_of_finite_tree := minimal_bad_seq size H 

theorem bad_mbs_finite_tree : ¬ is_good mbs_of_finite_tree embeds := badness_of_mbs size H

theorem ne_node_of_elt_of_mbs_finite_tree (n : ℕ) {ts : fin 0 → finite_tree} : mbs_of_finite_tree n ≠ cons ts :=
assume Hneg,
have cons ts  ≼ mbs_of_finite_tree (succ n), by apply node_embeds,
have Hr : mbs_of_finite_tree n ≼ mbs_of_finite_tree (succ n), by simph,
have n < succ n, from lt_succ_self n,
have is_good mbs_of_finite_tree embeds, from exists.intro n (exists.intro (succ n) (and.intro this Hr)),
show _, from bad_mbs_finite_tree this

theorem minimality_of_mbs_finite_tree0 (f : ℕ → finite_tree) (Hf : ¬ is_good f embeds) : size (mbs_of_finite_tree 0) ≤ size (f 0) := minimality_of_mbs_0 size H f Hf

theorem minimality_of_mbs_finite_tree (n : ℕ) (f : ℕ → finite_tree) (H1 : extends_at n mbs_of_finite_tree f ∧ ¬ is_good f embeds) : size (mbs_of_finite_tree (succ n)) ≤ size (f (succ n)) := minimality_of_mbs size H n f H1

definition seq_branches_of_mbs_tree (n : ℕ) : set (finite_tree × ℕ) := branches (mbs_of_finite_tree n)

theorem mem_of_seq_branches {n i : ℕ} (ts : fin n → finite_tree) (k : fin n) (Heq : mbs_of_finite_tree i = cons ts) : (ts k, val k) ∈ seq_branches_of_mbs_tree i :=
have ts k = (ts k, val k).1 ∧ val k = (ts k, val k).2, from and.intro rfl rfl,
have ∃ a, ts a = (ts k, val k).1 ∧ val a = (ts k, val k).2, from exists.intro k this,
have (ts k, val k) ∈ branches (cons ts), from this,
by rewrite -Heq at this;exact this

definition mbs_tree : Type := {t : finite_tree × ℕ // ∃ i, t ∈ seq_branches_of_mbs_tree i}

definition embeds' (t : mbs_tree) (s : mbs_tree) : Prop := t.val.1 ≼ s.val.1

theorem embeds'_refl (t : mbs_tree) : embeds' t t := embeds_refl t.val.1

theorem embeds'_trans (a b c : mbs_tree) : embeds' a b → embeds' b c → embeds' a c :=
assume H₁, assume H₂, embeds_trans H₁ H₂

section

parameter H' : ∃ f, ¬ is_good f embeds'

definition R : ℕ → mbs_tree := some H'

definition family_index (n : ℕ) : ℕ := some ((R n).2) 

definition index_set_of_mbs_tree : set ℕ := image family_index  univ

lemma index_ne_empty : index_set_of_mbs_tree ≠ ∅ := ne_empty_of_image_on_univ family_index

definition least_family_index := least index_set_of_mbs_tree index_ne_empty

lemma exists_least : ∃ i, family_index i = least_family_index :=
have least_family_index ∈ index_set_of_mbs_tree, from least_is_mem index_set_of_mbs_tree index_ne_empty,
let ⟨i,h⟩ := this in
⟨i, h^.right⟩

definition least_index : ℕ := some exists_least

definition Kruskal's_g (n : ℕ) : mbs_tree := R (least_index + n)

definition Kruskal's_h (n : ℕ) : ℕ :=  family_index (least_index + n)

theorem bad_Kruskal's_g : ¬ is_good Kruskal's_g embeds' :=
suppose is_good Kruskal's_g embeds',
let ⟨i,j,hij⟩ := this in
have Hr : embeds' (Kruskal's_g i) (Kruskal's_g j), from hij^.right,
have least_index + i < least_index + j, from add_lt_add_left hij^.left _,
have is_good R embeds', from ⟨least_index + i, ⟨least_index + j,⟨this, Hr⟩⟩⟩,
(some_spec H') this

theorem Kruskal's_Hg : ¬ is_good (fst ∘ (val ∘ Kruskal's_g)) embeds := bad_Kruskal's_g

theorem trans_of_Kruskal's_g {i j : ℕ} (H1 : mbs_of_finite_tree i ≼ (Kruskal's_g j).val.1) : 
mbs_of_finite_tree i ≼ mbs_of_finite_tree (Kruskal's_h j) := 
have (Kruskal's_g j).val ∈ branches (mbs_of_finite_tree (Kruskal's_h j)), from some_spec (Kruskal's_g j).2,
have (Kruskal's_g j).val.1 ≼ mbs_of_finite_tree (Kruskal's_h j), from embeds_of_branches this,
embeds_trans H1 this

theorem size_elt_Kruskal's_g_lt_mbs_finite_tree (n : ℕ) : size (Kruskal's_g n).val.1 < size (mbs_of_finite_tree (Kruskal's_h n)) := 
lt_of_size_of_branches (some_spec (Kruskal's_g n).2)

theorem Kruskal's_Hbp : size (Kruskal's_g 0).val.1 < size (mbs_of_finite_tree (Kruskal's_h 0)) := size_elt_Kruskal's_g_lt_mbs_finite_tree 0

lemma family_index_in_index_of_mbs_tree (n : ℕ) : Kruskal's_h n ∈ index_set_of_mbs_tree :=
have Kruskal's_h n = family_index (least_index + n), from rfl,
⟨(least_index + n),⟨trivial,rfl⟩⟩

theorem Kruskal's_Hh (n : ℕ) : Kruskal's_h 0 ≤ Kruskal's_h n :=
-- have Kruskal's_h 0 = family_index (least_index + 0), from rfl,
have Kruskal's_h 0 = family_index least_index, from rfl,--by simph,
have family_index least_index = least_family_index, from some_spec exists_least,
have Kruskal's_h 0 = least_family_index, by simph,
begin rw this, apply minimality, apply family_index_in_index_of_mbs_tree end

theorem Kruskal's_H : ∀ i j, mbs_of_finite_tree i ≼ (Kruskal's_g (j - Kruskal's_h 0)).val.1 → mbs_of_finite_tree i ≼ mbs_of_finite_tree (Kruskal's_h (j - Kruskal's_h 0)) := λ i j, λ H1, trans_of_Kruskal's_g H1

definition Kruskal's_comb_seq (n : ℕ) : finite_tree := @comb_seq_with_mbs _ embeds (fst ∘ (val ∘ Kruskal's_g)) Kruskal's_h size H n

theorem Kruskal's_local_contradiction : false := local_contra_of_comb_seq_with_mbs Kruskal's_h size Kruskal's_Hh H Kruskal's_Hg Kruskal's_H Kruskal's_Hbp

end

#check Kruskal's_local_contradiction

theorem embeds'_is_good : ∀ f, is_good f embeds' := 
by_contradiction
(suppose ¬ ∀ f, is_good f embeds',
 have ∃ f, ¬ is_good f embeds', from classical.exists_not_of_not_forall this,
 Kruskal's_local_contradiction this)

instance wqo_mbs_tree : wqo mbs_tree :=
wqo.mk (quasiorder.mk (has_le.mk embeds') embeds'_refl embeds'_trans) embeds'_is_good

definition wqo_finite_subsets_of_mbs_tree : wqo (finite_subsets mbs_tree) := wqo_finite_subsets

definition os : finite_subsets mbs_tree → finite_subsets mbs_tree → Prop := wqo_finite_subsets_of_mbs_tree.le

-- type mbs_tree is the collection of all branches at roots appearing in the mbs_of_finite_tree
-- hence, mbs_of_finite_tree can be viewed as a sequence on finite_subsets mbs_tree. We call this sequence a copy (or a mirror) of mbs_of_finite_tree.
-- the following theorem says given any sequence f : ℕ → finite_subsets mbs_tree,  there exists i j such that there exists a f' : mbs_tree → mbs_tree which is injective and nondescending from (f i) to (f j). 
theorem good_finite_subsets_of_mbs_tree : ∀ f, is_good f os := wqo_finite_subsets_of_mbs_tree.is_good

-- Intuitively, the above f' is already a witness of the goodness of mbs_of_finite_tree, as it maps each branch of mbs_of_finite_tree i to a branch of mbs_of_finite_tree j. (Also note that there is no node in the mbs_of_finite_tree.)

-- However, according to the definition of embeds, f' has to be of type fin n → fin m for some n,m ∈ ℕ, representing a permutation on the labels of the branches. The following construction recovers the desired function from f'.

-- branches at root of mbs_of_finite_tree form a set of mbs_tree
definition elt_copy_of_seq_branches (n : ℕ) : set mbs_tree := {x : mbs_tree | x.1 ∈ seq_branches_of_mbs_tree n}

theorem copy_refl_left (x : mbs_tree) (n : ℕ) : x ∈ elt_copy_of_seq_branches n → x.1 ∈ seq_branches_of_mbs_tree n := λ Hx, Hx

theorem copy_refl_right (x : mbs_tree) (n : ℕ) : x.1 ∈ seq_branches_of_mbs_tree n → x ∈ elt_copy_of_seq_branches n := λ Hx, Hx

instance  finite_seq_branches (n : ℕ) : finite (seq_branches_of_mbs_tree n) := finite_branches (mbs_of_finite_tree n)

theorem finite_elt (n : ℕ) : finite (elt_copy_of_seq_branches n) := 
have mapsto : maps_to subtype.val (elt_copy_of_seq_branches n) (seq_branches_of_mbs_tree n), from λ x Hx, copy_refl_left x n Hx,
have inj_on subtype.val (elt_copy_of_seq_branches n), from λ x₁ x₂ H₁ H₂, subtype.eq,
finite_of_inj_on mapsto this

-- this gives a sequence of finite_subsets of mbs_tree. 
-- copy_of_seq_branches 0 is the branches at the root of the first element of the minimal bad sequence of finite_tree.

definition copy_of_seq_branches (n : ℕ) : finite_subsets mbs_tree := ⟨elt_copy_of_seq_branches n, finite_elt n⟩

-- (copy_of_seq_branches i) is the collection of branches at the root of (mbs_of_finite_tree i)

theorem good_copy : ∃ i j, i < j ∧ os (copy_of_seq_branches i) (copy_of_seq_branches j) := good_finite_subsets_of_mbs_tree copy_of_seq_branches

section
-- destruct the statement: os (copy_of_seq_branches i) (copy_of_seq_branches j)
-- we want to show that there exists some i j such that (mbs_of_finite_tree i ≼ mbs_of_finite_tree j)
-- fortunately, i and j from good_copy suffice
-- this section tries to get an injection "recover" : fin ni → fin nj such that tsi ti ≼ tsj (recover ti) assuming that (mbs_of_finite_tree i = cons tsi) and (mbs_of_finite_tree j = cons tsj). Note that both are not nodes.
parameters {i j : ℕ}
-- -- since finite_subsets_of_mbs_tree is good, we have an injection f' from some set of branches to some set of branches. This is because each set of branches is a subset of mbs_tree.
parameter f' : mbs_tree → mbs_tree 
parameter inj : inj_from_to f' (elt_copy_of_seq_branches i) (elt_copy_of_seq_branches j)
-- -- of course, it is also nondescending by definition.
parameter nond : ∀ a : mbs_tree, a.val ∈ seq_branches_of_mbs_tree i → a.val.1 ≼ (f' a).val.1 ∧  (f' a).val ∈ seq_branches_of_mbs_tree j
-- suppose (mbs_of_finite_tree i) is of the form (cons tsi)
parameters ni nj : ℕ
parameters (tsi : fin ni → finite_tree) (tsj : fin nj → finite_tree)
-- suppose we know that they are destructed
parameter eqi : mbs_of_finite_tree i = cons tsi
parameter eqj : mbs_of_finite_tree j = cons tsj
-- this reminds us that each branch at the root of (mbs_of_finite_tree i) is in (seq_branches_of_mbs_tree i)
parameter Htsi : ∀ a, (tsi a, val a) ∈ seq_branches_of_mbs_tree i

lemma eltini (ti : fin ni) : (tsi ti, val ti) ∈ seq_branches_of_mbs_tree i := Htsi ti

-- every ti corresponds to some seq_branches_of_mbs_tree i
lemma pmbsa (ti : fin ni) : ∃ i, (tsi ti, val ti) ∈ seq_branches_of_mbs_tree i := ⟨i,eltini ti⟩

-- given a ti, find the corresponding mbs_tree of (tsi ti). The intuition is that this mbs_tree is itself, but of a different type.
definition mbst_form (ti : fin ni) : mbs_tree := ⟨(tsi ti, val ti),(pmbsa ti)⟩

theorem mem_mbst_form (a : fin ni) : mbst_form a ∈ elt_copy_of_seq_branches i := eltini a

theorem eq_of_mbst_form {a₁ a₂ : fin ni} (Heq : mbst_form a₁ = mbst_form a₂) : a₁ = a₂ :=
by apply eq_of_veq;super

-- lemma mem (ti : fin ni) : (f' (mbst_form ti)).val ∈ branches (mbs_of_finite_tree j) := 
-- (nond _ (begin dsimp [mbst_form], apply Htsi end))^.right
include eqj

-- recover : 
-- 1. find the mbst_form of ti, say x. 
-- 2. By nond, we know that (f' x) is in (seq_branches_of_mbs_tree j). 
-- 3. (seq_branches_of_mbs_tree j) is just branches (mbs_of_finite_tree j). 
-- 4. The latter is just (set_of_branches tsj). 
-- 5. This means that some a : fin nj corresponds to ti. 6. By choice, take such a fin nj.

definition recover (ti : fin ni) : fin nj :=
have (f' (mbst_form ti)).val ∈ seq_branches_of_mbs_tree j, from (nond _ (begin dsimp [mbst_form], apply Htsi end))^.right,
have mem : (f' (mbst_form ti)).val ∈ branches (mbs_of_finite_tree j), from this, -- this line is redundant
have branches (mbs_of_finite_tree j) = branches (cons tsj), by rw eqj, -- by rewrite eqj at this{2};exact this, 
have branches (mbs_of_finite_tree j) = branches_aux tsj, from this,
have (f' (mbst_form ti)).val ∈ branches_aux tsj, by rewrite this at mem;exact mem,
have ∃ a : fin nj, tsj a = (f' (mbst_form ti)).val.1 ∧ val a = (f' (mbst_form ti)).val.2, from this,
some this

theorem perm_recover (ti : fin ni) : tsi ti ≼ tsj (recover ti) := 
have (f' (mbst_form ti)).val ∈ seq_branches_of_mbs_tree j, from (nond _ (begin dsimp [mbst_form], apply Htsi end))^.right,
have mem : (f' (mbst_form ti)).val ∈ branches (mbs_of_finite_tree j), from this,
have branches (mbs_of_finite_tree j) = branches (mbs_of_finite_tree j), from rfl,
have branches (mbs_of_finite_tree j) = branches (cons tsj), by rw eqj, -- by rewrite eqj at this{2};exact this, 
have branches (mbs_of_finite_tree j) = branches_aux tsj, from this,
have (f' (mbst_form ti)).val ∈ branches_aux tsj, by rewrite this at mem;exact mem,
have ∃ a : fin nj, tsj a = (f' (mbst_form ti)).val.1 ∧ val a =  (f' (mbst_form ti)).val.2, from this,
have tsj (recover ti) = (f' (mbst_form ti)).val.1, from let ⟨a,b⟩ := some_spec this in a,
have tsi ti ≼ (f' (mbst_form ti)).val.1, from (nond _ (begin dsimp [mbst_form], apply Htsi end))^.left,
by simph

theorem inj_recover : injective recover := 
take a₁ a₂, assume Heq,
have (f' (mbst_form a₁)).val ∈ seq_branches_of_mbs_tree j, from (nond _ (begin dsimp [mbst_form], apply Htsi end))^.right,
have mem : (f' (mbst_form a₁)).val ∈ branches (mbs_of_finite_tree j), from this,
have branches (mbs_of_finite_tree j) = branches (mbs_of_finite_tree j), from rfl,
have branches (mbs_of_finite_tree j) = branches (cons tsj), by rw eqj, -- by rewrite eqj at this{2};exact this, 
have branches (mbs_of_finite_tree j) = branches_aux tsj, from this,
have (f' (mbst_form a₁)).val ∈ branches_aux tsj, by rewrite this at mem;exact mem,

have eeq1 : ∃ a : fin nj, tsj a = (f' (mbst_form a₁)).val.1 ∧ val a = (f' (mbst_form a₁)).val.2, from this,
have pr11 : tsj (recover a₁) = (f' (mbst_form a₁)).val.1, from let ⟨a,b⟩ := some_spec eeq1 in a,-- proof and.left (some_spec eeq1) qed,
have pr21 : val (recover a₁) = (f' (mbst_form a₁)).val.2, from let ⟨a,b⟩ := some_spec eeq1 in b, -- proof and.right (some_spec eeq1) qed,
have (f' (mbst_form a₂)).val ∈ seq_branches_of_mbs_tree j, from (nond _ (begin dsimp [mbst_form], apply Htsi end))^.right,-- proof and.right (nond _ (eltini a₂)) qed,
have mem : (f' (mbst_form a₂)).val ∈ branches (mbs_of_finite_tree j), from this,
have branches (mbs_of_finite_tree j) = branches (mbs_of_finite_tree j), from rfl,
have branches (mbs_of_finite_tree j) = branches (cons tsj), by rw eqj, -- by+ rewrite eqj at this{2};exact this, 
have branches (mbs_of_finite_tree j) = branches_aux tsj, from this,
have (f' (mbst_form a₂)).val ∈ branches_aux tsj, by rewrite this at mem;exact mem,
have eeq2 : ∃ a : fin nj, tsj a = (f' (mbst_form a₂)).val.1 ∧ val a = (f' (mbst_form a₂)).val.2, from this,
have pr12 : tsj (recover a₂) = (f' (mbst_form a₂)).val.1,  from let ⟨a,b⟩ := some_spec eeq2 in a,-- proof and.left (some_spec eeq2) qed,
have pr22 : val (recover a₂) = (f' (mbst_form a₂)).val.2, from let ⟨a,b⟩ := some_spec eeq2 in b,-- proof and.right (some_spec eeq2) qed,
have eq1 : (f' (mbst_form a₁)).val.1 = (f' (mbst_form a₂)).val.1, by rw [-pr12, -pr11, Heq],
have (f' (mbst_form a₁)).val.2 = (f' (mbst_form a₂)).val.2, by rw [-pr22,-pr21,Heq],
have (f' (mbst_form a₁)).val = (f' (mbst_form a₂)).val, from eq_of_prod eq1 this,
have f'eq : f' (mbst_form a₁) = f' (mbst_form a₂), from subtype.eq this,
have ∀ x₁ x₂ : mbs_tree, x₁ ∈ elt_copy_of_seq_branches i → x₂ ∈ elt_copy_of_seq_branches i → f' x₁ = f' x₂ → x₁ = x₂, from and.right inj,
have mbst_form a₁ = mbst_form a₂, from this (mbst_form a₁) (mbst_form a₂) (mem_mbst_form a₁) (mem_mbst_form a₂) f'eq,
show _, from eq_of_mbst_form this

end

#check @recover
#check inj_recover

theorem good_mbs_of_finite_tree :  ∃ i j, i < j ∧ mbs_of_finite_tree i ≼ mbs_of_finite_tree j :=
let ⟨i,j,⟨iltj,⟨f',⟨inj,nond⟩⟩⟩⟩ := good_copy in
let ⟨ni,tsi,htsi⟩ := @finite_tree_destruct (mbs_of_finite_tree i) in
let ⟨nj,tsj,htsj⟩ := @finite_tree_destruct (mbs_of_finite_tree j) in
have Htsi : ∀ a, (tsi a, val a) ∈ seq_branches_of_mbs_tree i, from take a, mem_of_seq_branches tsi a htsi,
let f (a : fin ni) : fin nj := recover f' nond ni _ tsi tsj htsj Htsi a in
have injf : injective f, from inj_recover _ inj _ _ _ _ _ _ _,
have ∀ z : fin ni, tsi z ≼ tsj (f z), from λ z, perm_recover _ _ _ _ _ _ _ _ _,
have cons tsi ≼ cons tsj, from or.inr ⟨f,⟨injf,this⟩⟩,
have mbs_of_finite_tree i ≼ mbs_of_finite_tree j, by simph,
⟨i,j,⟨iltj,this⟩⟩

theorem Kruskal's_contradiction : false := bad_mbs_finite_tree good_mbs_of_finite_tree

end

theorem embeds_is_good : ∀ f, is_good f embeds :=
by_contradiction
(suppose ¬ ∀ f, is_good f embeds,
 have ∃ f, ¬ is_good f embeds, from classical.exists_not_of_not_forall this,
 Kruskal's_contradiction this)

def wqo_finite_tree : wqo finite_tree :=
wqo.mk (quasiorder.mk (has_le.mk embeds) embeds_refl @embeds_trans) embeds_is_good


