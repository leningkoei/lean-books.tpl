section useful
  -- domain of `variable`s is `section`
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩ -- Sigma.mk a b
def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  ⟨a, b⟩ -- Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (λ α ↦ α) Nat x).2

#check id Nat
#check @id Nat
