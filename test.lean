structure quasiorder (A : Type) extends has_le A :=
(refl : ∀ a, le a a)
(trans : ∀ {a b c}, le a b → le b c → le a c)

structure wqo (A : Type) extends quasiorder A :=
(is_good : ∀ f : ℕ → A, ∃ i j : ℕ, i < j ∧ le (f i) (f j))

-- the following works but the above does no.t

-- variable {A : Type}

-- structure has_refl (R : A → A → Prop) : Prop :=
-- (refl : ∀ a, R a a)

-- structure is_equiv (R : A → A → Prop) extends has_refl R : Prop :=
-- (symm : ∀ a b, R a b → R b a)
-- (trans : ∀ a b c, R a b → R b c → R a c)

-- structure is_g (R : A → A → Prop) extends is_equiv R : Prop
