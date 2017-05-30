universe variables u v

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


  section exact
  variable {A : Type u}
  variable [s : setoid A]
  include s

  private definition rel (q₁ q₂ : quotient s) : Prop :=
  quot.lift_on₂ q₁ q₂
    (λ a₁ a₂, a₁ ≈ a₂)
    (λ a₁ a₂ b₁ b₂ a₁b₁ a₂b₂,
      propext (iff.intro
        (λ a₁a₂, setoid.trans (setoid.symm a₁b₁) (setoid.trans a₁a₂ a₂b₂))
        (λ b₁b₂, setoid.trans a₁b₁ (setoid.trans b₁b₂ (setoid.symm a₂b₂)))))

  local infix `~` := rel

  private lemma rel.refl : ∀ q : quotient s, q ~ q :=
  λ q, quot.induction_on q (λ a, setoid.refl a)

  private lemma eq_imp_rel {q₁ q₂ : quotient s} : q₁ = q₂ → q₁ ~ q₂ :=
  assume h, eq.rec_on h (rel.refl q₁)

  theorem exact' {a b : A} : ⟦a⟧ = ⟦b⟧ → a ≈ b :=
  assume h, eq_imp_rel h

  end exact


  section
  universe variables u_a u_b u_c
  variables {A : Type u_a} {B : Type u_b}
  variables [s₁ : setoid A] [s₂ : setoid B]
  include s₁ s₂

  attribute [reducible, elab_as_eliminator]
  protected definition rec_on_subsingleton₂
     {C : quotient s₁ → quotient s₂ → Type u_c} [H : ∀ a b, subsingleton (C ⟦a⟧ ⟦b⟧)]
     (q₁ : quotient s₁) (q₂ : quotient s₂) (f : Π a b, C ⟦a⟧ ⟦b⟧) : C q₁ q₂:=
  @quot.rec_on_subsingleton _ s₁.r (λ q, C q q₂) (λ a, quot.ind (λ b, H a b) q₂) q₁
    (λ a, @quot.rec_on_subsingleton _ s₂.r _ (H a) q₂ (λ b, f a b))

end

end quot
