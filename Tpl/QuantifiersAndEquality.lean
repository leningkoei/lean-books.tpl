section TheUniversalQuantifier

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  show (∀ x : α, p x ∧ q x) → ∀ y : α, p y from λ h : ∀ x : α, p x ∧ q x ↦
  show ∀ y : α, p y from λ y : α ↦
  show p y from (h y).left

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)
variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)
#check trans_r
#check trans_r hab
#check trans_r hab hbc

variable (α : Sort 1)
variable (β : Sort 0)
#check α → β
#check (α : Sort 1) → (β : Sort 0)
#check (α : Sort 1) → Sort 0

end TheUniversalQuantifier

section Equality

universe u
#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

variable (α : Type) (a b c d : α) -- Type is Sort 1, α is Sort 0(Prop)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)
example : a = d :=
  show a = d from Eq.trans (show a = b from hab) $
  show b = d from Eq.trans (show b = c from Eq.symm hcb) $
  show c = d from hcd
example : a = d :=
  show a = d from (show a = b from hab).trans $
  show b = d from (show b = c from hcb.symm).trans $
  show c = d from hcd

variable (α β : Type)
example (f : α → β) (a : α) : (λ x ↦ f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
example : Eq.refl wtf = rfl := rfl

example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  -- Eq.subst h1 h2 -- Almost as same as below.
  h1 ▸ h2

variable (α : Type)
variable (a b : α)
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)
example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

#check Nat.add_mul
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h₁ : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h₂ : (x + y) * x = x * x + y * x := Nat.add_mul x y x
  -- have h₃ : (x + y) * (x + y) = (x * x + y * x) + (x + y) * y := h₂ ▸ h₁
  have h₄ : (x + y) * y = x * y + y * y := Nat.add_mul x y y
  -- have h₅ : (x + y) * (x + y) = (x * x + y * x) + (x * y + y * y) := h₄ ▸ h₃
  have h₅ : (x + y) * (x + y) = (x * x + y * x) + (x * y + y * y) :=
    h₂ ▸ h₄ ▸ h₁
  have h₆ : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) := h₅
  have h₇ : x * x + y * x + x * y + y * y = x * x + y * x + (x * y + y * y) :=
    Nat.add_assoc (x * x + y * x) (x * y) (y * y)
  -- have h₈ : x * x + y * x + (x * y + y * y) = x * x + y * x + x * y + y * y :=
  --   h₇.symm
  -- h₈ ▸ h₆
  h₇ ▸ h₆

end Equality

section CalculationalProofs
end CalculationalProofs

section TheExistentialQuantifier
end TheExistentialQuantifier

section MoreOnTheProofLanguage
end MoreOnTheProofLanguage

section Exercises
end Exercises

