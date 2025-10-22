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

end Equality

section CalculationalProofs
end CalculationalProofs

section TheExistentialQuantifier
end TheExistentialQuantifier

section MoreOnTheProofLanguage
end MoreOnTheProofLanguage

section Exercises
end Exercises

