import tools.super

theorem iff.of_eq {a b : Prop} (h : a = b) : a ↔ b :=
eq.rec_on h iff.rfl



theorem and.left_distrib (a b c : Prop) : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) := by super

theorem and.right_distrib (a b c : Prop) : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := by super

theorem or.left_distrib (a b c : Prop) : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) := by super

theorem or.right_distrib (a b c : Prop) : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) := by super
