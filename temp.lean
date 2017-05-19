open nat function

inductive finite_tree : Type
| cons : Π {n : ℕ},  (fin n → finite_tree) → finite_tree

namespace finite_tree

inductive embeds : finite_tree → finite_tree → Prop
| node_embeds {t : finite_tree} {ts : fin 0 → finite_tree} : embeds (@cons 0 ts) t
| to_subtree {t : finite_tree} {n : ℕ} {ts : fin n → finite_tree} {i : fin n} (h : embeds t (ts i)) : embeds t (cons ts)
| to_top     {m : ℕ} {ts : fin m → finite_tree} {n : ℕ} {us : fin n → finite_tree}
             {f : fin m → fin n} (injf : injective f) (h : ∀ i, embeds (ts i) (us (f i))) :
                 embeds (cons ts) (cons us)

infix ` ≼ `:50 := embeds  -- \preceq

theorem foo {n : ℕ} {ts : fin (succ n) → finite_tree} 
{tt : fin 0 → finite_tree}: ¬ cons ts ≼ cons tt := 
begin intro h, cases h, end -- Renaming is not working on my computer

-- The following does not work either. Can we do induction manually without invoking the tactic mode?

-- λ h, embeds.cases_on h _
-- λ h, embeds.rec_on h _


end finite_tree
