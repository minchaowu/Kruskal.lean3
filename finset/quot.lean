namespace quot

section
  universe variables u_a u_b u_c
  variables {A : Type u_a} {B : Type u_b} {C : Type u_c}
  variables [s₁ : setoid A] [s₂ : setoid B]

  include s₁ s₂

  attribute [reducible, elab_as_eliminator]
  protected definition lift₂
     (f : A → B → C)(c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
     (q₁ : quotient s₁) (q₂ : quotient s₂) : C :=
  quot.lift
    (λ (a₁ : A), quot.lift (f a₁) (λ (a b : B), c a₁ a a₁ b (setoid.refl a₁)) q₂)
    (λ (a b : A) (H : a ≈ b),
       @quot.ind B s₂.r
         (λ (a_1 : quotient s₂),
            (quot.lift (f a) (λ (a_1 b : B), c a a_1 a b (setoid.refl a)) a_1)
            =
            (quot.lift (f b) (λ (a b_1 : B), c b a b b_1 (setoid.refl b)) a_1))
         (λ (a' : B), c a a' b a' H (setoid.refl a'))
         q₂)
    q₁

  attribute [reducible, elab_as_eliminator]
  protected definition lift_on₂ (q₁ : quotient s₁) (q₂ : quotient s₂) (f : A → B → C) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : C :=
quot.lift₂ f c q₁ q₂

  attribute [elab_as_eliminator]
  protected theorem induction_on₂ {C : quotient s₁ → quotient s₂ → Prop} (q₁ : quotient s₁) (q₂ : quotient s₂) (H : ∀ a b, C ⟦a⟧ ⟦b⟧) : C q₁ q₂ :=
quot.ind (λ a₁, quot.ind (λ a₂, H a₁ a₂) q₂) q₁


  attribute [elab_as_eliminator]
  protected theorem induction_on₃
     [s₃ : setoid C]
     {D : quotient s₁ → quotient s₂ → quotient s₃ → Prop} (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃) (H : ∀ a b c, D ⟦a⟧ ⟦b⟧ ⟦c⟧)
     : D q₁ q₂ q₃ :=
quot.ind (λ a₁, quot.ind (λ a₂, quot.ind (λ a₃, H a₁ a₂ a₃) q₃) q₂) q₁


end


end quot
