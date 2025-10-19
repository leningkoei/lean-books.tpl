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

end TheUniversalQuantifier

