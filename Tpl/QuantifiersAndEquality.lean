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

#check Eq.subst
example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  -- Eq.subst h1 h2 -- Almost as same as below.
  h1 ▸ h2

#check congrArg
#check congrFun
#check congr
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

#check Nat.add_zero
#check Nat.zero_add
#check Nat.mul_one
#check Nat.one_mul
#check Nat.add_comm
#check Nat.add_assoc
#check Nat.mul_comm
#check Nat.mul_assoc
#check Nat.mul_add
#check Nat.add_mul
#check Nat.left_distrib
#check Nat.right_distrib

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

theorem T
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
: a = e := calc
  a = b     := h1
  _ = c + 1 := h2
  _ = d + 1 := congrArg Nat.succ h3
  _ = 1 + d := Nat.add_comm d 1
  _ = e := Eq.symm h4

theorem T'
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
: a = e := calc
  a = b     := by rw [h1]
  _ = c + 1 := by rw [h2]
  _ = d + 1 := by rw [h3]
  _ = 1 + d := by rw [Nat.add_comm]
  _ = e     := by rw [h4]

theorem T''
  (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
: a = e := calc
  -- a = e := by rw [h1, h2, h3, Nat.add_comm, h4]
  a = e := by simp [h1, h2, h3, Nat.add_comm, h4]

variable (a b c d : Nat)
variable (h1 : a = b)
variable (h2 : b ≤ c)
variable (h3 : c + 1 < d)
example : a < d := calc
  a = b     := h1
  _ ≤ c     := h2
  _ < c + 1 := Nat.lt_succ_self c
  _ < d     := h3

def divides (x y : Nat) : Prop :=
  ∃ k, k * x = y
def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩
def divides_mul (x : Nat) (k : Nat) : divides x (k * x) := ⟨k, rfl⟩
instance : Trans divides divides divides where
  trans := divides_trans
example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) := calc
  divides x y       := h₁
  y = z             := h₂
  divides z (2 * z) := divides_mul ..
infix:50 " | " => divides
example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) := calc
  x | y       := h₁
  _ = z       := h₂
  _ | (2 * z) := divides_mul ..

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y := Nat.mul_add (x + y) x y
    -- _ = x * x + y * x + (x + y) * y := by rw [Nat.add_mul]
    _ = x * x + y * x + (x + y) * y :=
      congrArg (· + (x + y) * y) $ Nat.add_mul x y x
    _ = x * x + y * x + (x * y + y * y) :=
      congrArg (x * x + y * x + ·) $ Nat.add_mul x y y
    _ = x * x + y * x + x * y + y * y :=
      Eq.symm $ Nat.add_assoc (x * x + y * x) (x * y) (y * y)

end CalculationalProofs

section TheExistentialQuantifier

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

#check And.intro
example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

-- {α : Sort u} {p : α → Prop} Exists p = ∃ α, Prop
#check Exists.intro
#check @Exists.intro
#check Exists.elim

example (α : Type) (p q : α → Prop) (h : ∃ x : α, p x ∧ q x)
: ∃ x : α, q x ∧ p x := Exists.elim h $
  show ∀ a : α, p a ∧ q a → ∃ a, q a ∧ p a from λ w : α ↦
  show p w ∧ q w → ∃ w, q w ∧ p w from λ hw : p w ∧ q w ↦
  -- show ∃ w, q w ∧ p w from Exists.intro w (And.intro hw.right hw.left)
  -- show ∃ w, q w ∧ p w from Exists.intro w ⟨hw.right, hw.left⟩
  -- show ∃ w, q w ∧ p w from ⟨w, ⟨hw.right, hw.left⟩⟩
  show ∃ w, q w ∧ p w from ⟨w, hw.right, hw.left⟩

example (α : Type) (p q : α → Prop) (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | Exists.intro (w : α) (hw : p w ∧ q w) => ⟨w, hw.right, hw.left⟩
  -- | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

example (α : Type) (p q : α → Prop) (h : ∃ x : α, p x ∧ q x)
: ∃ x : α, q x ∧ p x :=
  -- let (Exists.intro w (And.intro hpw hqw)) := h
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

example (α : Type) (p q : α → Prop)
: (∃ x : α, p x ∧ q x) → (∃ x : α, q x ∧ p x) :=
  λ (Exists.intro w (And.intro hpw hqw)) => ⟨w, hqw, hpw⟩

#check Exists.intro
def is_even (a : Nat) := ∃ b : Nat, a = 2 * b
theorem even_plus_even {a b : Nat} (h₁ : is_even a) (h₂ : is_even b)
: is_even (a + b) :=
  show is_even (a + b) from Exists.elim h₁ $
  show ∀ w₁ : Nat, a = 2 * w₁ → is_even (a + b) from λ w₁ : Nat ↦
  show a = 2 * w₁ → is_even (a + b) from λ hw₁ : a = 2 * w₁ ↦
  show is_even (a + b) from Exists.elim h₂ $
  show ∀ w₂ : Nat, b = 2 * w₂ → is_even (a + b) from λ w₂ : Nat ↦
  show b = 2 * w₂ → is_even (a + b) from λ hw₂ : b = 2 * w₂ ↦
  show is_even (a + b) from Exists.intro (w₁ + w₂) $
  show a + b = 2 * (w₁ + w₂) from
    calc a + b
      _ = 2 * w₁ + b := congrArg (· + b) $ hw₁
      _ = 2 * w₁ + 2 * w₂ := congrArg (2 * w₁ + ·) $ hw₂
      _ = 2 * (w₁ + w₂) := Eq.symm $ Nat.mul_add 2 w₁ w₂
theorem even_plus_even' {a b : Nat} (h₁ : is_even a) (h₂ : is_even b)
: is_even (a + b) :=
  match h₁, h₂ with
  | ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩ => ⟨w₁ + w₂, by rw [hw₁, hw₂, Nat.mul_add]⟩

#check Classical.byContradiction
open Classical in
example {α : Sort u} (p : α → Prop) (h : ¬(∀ x : α, ¬p x)) : ∃ x : α, p x :=
  byContradiction $
    show (¬∃ x : α, p x) → False from λ h₁ : ¬∃ x : α, p x ↦
    show False from h $
    show ∀ x : α, ¬p x from λ x : α ↦
    show ¬p x from
    show p x → False from λ h₃ : p x ↦
    have h₄ : ∃ x : α,  p x := Exists.intro x h₃
    show False from h₁ h₄

example (α : Type) (r : Prop) : (∃ _x : α, r) → r :=
  show (∃ _x : α, r) → r from λ h : ∃ _x : α, r ↦
  show r from Exists.elim h $
  show ∀ _w : α, r → r from λ _w : α ↦
  show r → r from λ hr : r ↦
  show r from hr

example (α : Type) (r : Prop) (a : α) : r → (∃ _x : α, r) :=
  show r → (∃ _x : α, r) from λ hr : r ↦
  show ∃ _x : α, r from Exists.intro a hr

#check Exists.intro
#check Exists.elim
example (α : Type) (p : α → Prop) (r : Prop)
: (∃ x : α, p x ∧ r) ↔ (∃ x : α, p x) ∧ r :=
  have h₁ : (∃ x : α, p x ∧ r) → (∃ x : α, p x) ∧ r :=
    show (∃ x : α, p x ∧ r) → (∃ x : α, p x) ∧ r from λ h₁ : ∃ x : α, p x ∧ r ↦
    show (∃ x : α, p x) ∧ r from Exists.elim h₁ $
    show ∀ w : α, p w ∧ r → (∃ x : α, p x) ∧ r from λ w : α ↦
    show p w ∧ r → (∃ x : α, p x) ∧ r from λ h₁ : p w ∧ r ↦
    have h_left : ∃ w : α, p w := Exists.intro w h₁.left
    show (∃ w : α, p w) ∧ r from And.intro h_left h₁.right
  have h₂ : (∃ x : α, p x) ∧ r → (∃ x : α, p x ∧ r) :=
    show _ from λ h₂ : (∃ x : α, p x) ∧ r ↦
    have h_left : ∃ x : α, p x := h₂.left
    have hr : r := h₂.right
    show ∃ x : α, p x ∧ r from Exists.elim h_left $
    show ∀ w : α, p w → ∃ x : α, p x ∧ r from λ w : α ↦
    show p w → ∃ x : α, p x ∧ r from λ hp : p w ↦
    show ∃ x : α, p x ∧ r from Exists.intro w $
    show p w ∧ r from And.intro hp hr
  Iff.intro h₁ h₂

#check Or.elim
example (α : Type) (p q : α → Prop)
: (∃ x : α, p x ∨ q x) ↔ (∃ x : α, p x) ∨ (∃ x : α, q x) :=
  have hlr : (∃ x : α, p x ∨ q x) → (∃ x : α, p x) ∨ (∃ x : α, q x) :=
    λ hl : ∃ x : α, p x ∨ q x ↦
    show (∃ x : α, p x) ∨ (∃ x : α, q x) from Exists.elim hl $
    show ∀ w : α, p w ∨ q w → (∃ x : α, p x) ∨ (∃ x : α, q x) from λ w : α ↦
    show p w ∨ q w → (∃ x : α, p x) ∨ (∃ x : α, q x) from λ hpq : p w ∨ q w ↦
    have hp : p w → (∃ x : α, p x) ∨ (∃ x : α, q x) := λ hp : p w ↦
      show (∃ x : α, p x) ∨ (∃ x : α, q x) from Or.inl $
      show ∃ x : α, p x from Exists.intro w $
      show p w from hp
    have hq : q w → (∃ x : α, p x) ∨ (∃ x : α, q x) := λ hq : q w ↦
      show (∃ x : α, p x) ∨ (∃ x : α, q x) from Or.inr $
      show ∃ x : α, q x from Exists.intro w $
      show q w from hq
    show (∃ x : α, p x) ∨ (∃ x : α, q x) from Or.elim hpq hp hq
  have hrl : (∃ x : α, p x) ∨ (∃ x : α, q x) → (∃ x : α, p x ∨ q x) :=
    λ hr : (∃ x : α, p x) ∨ (∃ x : α, q x) ↦
    have hp : (∃ x : α, p x) → ∃ x : α, p x ∨ q x := λ hp : ∃ x : α, p x ↦
      show ∃ x : α, p x ∨ q x from Exists.elim hp $
      show ∀ w : α, p w → ∃ x : α, p x ∨ q x from λ w : α ↦
      show p w → ∃ x : α, p x ∨ q x from λ hp : p w ↦
      show ∃ x : α, p x ∨ q x from Exists.intro w $
      show p w ∨ q w from Or.inl $
      show p w from hp
    have hq : (∃ x : α, q x) → ∃ x : α, p x ∨ q x := λ hq : ∃ x : α, q x ↦
      show ∃ x : α, p x ∨ q x from Exists.elim hq $
      show ∀ w : α, q w → ∃ x : α, p x ∨ q x from λ w : α ↦
      show q w → ∃ x : α, p x ∨ q x from λ hq : q w ↦
      show ∃ x : α, p x ∨ q x from Exists.intro w $
      show p w ∨ q w from Or.inr $
      show q w from hq
    show ∃ x : α, p x ∨ q x from Or.elim hr hp hq
  Iff.intro hlr hrl

#check Classical.byContradiction
example (α : Type) (p : α → Prop) : (∀ x : α, p x) ↔ ¬(∃ x : α, ¬p x) :=
  have hlr : (∀ x : α, p x) → ¬(∃ x : α, ¬p x) := λ hp : ∀ x : α, p x ↦
    show ¬(∃ x : α, ¬p x) from
    show (∃ x : α, p x → False) → False from λ hnp : ∃ x : α, p x → False ↦
    show False from Exists.elim hnp $
    show ∀ w : α, (p w → False) → False from λ w : α ↦
    show (p w → False) → False from λ hnp : p w → False ↦
    have hp : p w :=
      have hp : (x : α) → p x := hp
      show p w from hp w
    show False from hnp hp
  have hrl : ¬(∃ x : α, ¬p x) → (∀ x : α, p x) :=
    λ h : (∃ x : α, ¬p x) → False ↦
    show ∀ x : α, p x from λ w : α ↦
    show p w from Classical.byContradiction $
    show ¬p w → False from λ hnp : ¬p w ↦
    show False from h $
    show ∃ x : α, ¬p x from Exists.intro w $
    show ¬p w from hnp
  Iff.intro hlr hrl

example (α : Type) (p : α → Prop) : (∃ x : α, p x) ↔ ¬∀ x : α, ¬p x :=
  have hlr : (∃ x : α, p x) → ¬∀ x : α, ¬p x := λ h : ∃ x : α, p x ↦
    show (∀ x : α, ¬p x) → False from λ h' : ∀ x : α, ¬p x ↦
    show False from Exists.elim h $
    show ∀ w : α, p w → False from λ w : α ↦
    show p w → False from
    have h' : (x : α) → ¬p x := h'
    have hnp : ¬p w := h' w
    have hnp : p w → False := hnp
    show p w → False from hnp
  have hrl : (¬∀ x : α, ¬p x) → ∃ x : α, p x := λ h : (∀ x : α, ¬p x) → False ↦
    show ∃ x : α, p x from Classical.byContradiction $
    show (¬∃ x : α, p x) → False from λ h' : ¬∃ x : α, p x ↦
    show False from h $
    show ∀ x : α, ¬p x from λ w : α ↦
    show ¬p w from
    show p w → False from λ hp : p w ↦
    show False from h' $
    show ∃ x : α, p x from Exists.intro w $
    show p w from hp
  Iff.intro hlr hrl

example (α : Type) (p : α → Prop) : (¬∃ x : α, p x) ↔ (∀ x : α, ¬p x) :=
  have hlr : (¬∃ x : α, p x) → ∀ x : α, ¬p x := λ hn : (∃ x : α, p x) → False ↦
    show ∀ x : α, ¬p x from λ w : α ↦
    show p w → False from λ hp : p w ↦
    show False from hn $
    show ∃ x : α, p x from Exists.intro w $
    show p w from hp
  have hrl : (∀ x : α, ¬p x) → ¬∃ x : α, p x := λ h : ∀ x : α, ¬p x ↦
    show (∃ x : α, p x) → False from λ hp : ∃ x : α, p x ↦
    show False from Exists.elim hp $
    show ∀ w : α, p w → False from λ w : α ↦
    show p w → False from λ hp : p w ↦
    have hnp : p w → False :=
      have hnp : (x : α) → p x → False := h
      show p w → False from hnp w
    show False from hnp hp
  Iff.intro hlr hrl

example (α : Type) (p : α → Prop) : (¬∀ x : α, p x) ↔ (∃ x : α, ¬p x) :=
  have hlr : (¬∀ x : α, p x) → ∃ x : α, ¬p x := λ hnp : (∀ x : α, p x) → False ↦
    show ∃ x : α, ¬p x from Classical.byContradiction $
    show (¬∃ x : α, ¬p x) → False from λ hnp' : (∃ x : α, ¬p x) → False ↦
    show False from hnp $
    show ∀ x : α, p x from λ w : α ↦
    show p w from Classical.byContradiction $
    show ¬p w → False from λ hnp : ¬p w ↦
    show False from hnp' $
    show ∃ x : α, ¬p x from Exists.intro w $
    show ¬p w from hnp
  have hrl : (∃ x : α, ¬p x) → ¬∀ x : α, p x := λ hr : ∃ x : α, ¬p x ↦
    show (∀ x : α, p x) → False from λ hp : ∀ x : α, p x ↦
    show False from Exists.elim hr $
    show ∀ w : α, ¬p w → False from λ w : α ↦
    show ¬p w → False from λ hnp : ¬p w ↦
    show False from hnp $
    have hp : (x : α) → p x := hp
    have hp : p w := hp w
    show p w from hp
  Iff.intro hlr hrl

example (α : Type) (p : α → Prop) (r : Prop)
: (∀ x : α, p x → r) ↔ (∃ x : α, p x) → r :=
  have hlr : (∀ x : α, p x → r) → (∃ x : α, p x) → r :=
    λ hl : ∀ x : α, p x → r ↦
    show (∃ x : α, p x) → r from λ hrl : ∃ x : α, p x ↦
    show r from Exists.elim hrl $
    show ∀ w : α, p w → r from λ w : α ↦
    show p w → r from λ hp : p w ↦
    show r from
      have hl : (x : α) → p x → r := hl
      have hr : r := hl w hp
    show r from hr
  have hrl : ((∃ x : α, p x) → r) → ∀ x : α, p x → r :=
    λ hr : (∃ x : α, p x) → r ↦
    show ∀ x : α, p x → r from λ w : α ↦
    show p w → r from λ hp : p w ↦
    show r from hr $
    show ∃ x : α, p x from Exists.intro w $
    show p w from hp
  Iff.intro hlr hrl

example (α : Type) (p : α → Prop) (r : Prop) (a : α)
: (∃ x : α, p x → r) ↔ (∀ x : α, p x) → r :=
  have hlr : (∃ x : α, p x → r) → (∀ x : α, p x) → r :=
    λ hl : ∃ x : α, p x → r ↦
    λ hrl : ∀ x : α, p x ↦
    show r from Exists.elim hl $
    show ∀ w : α, (p w → r) → r from λ w : α ↦
    show (p w → r) → r from λ h : p w → r ↦
    show r from h $
    show p w from
      have hrl : (x : α) → p x := hrl
      have hp : p w := hrl w
    show p w from hp
  have hrl : ((∀ x : α, p x) → r) → ∃ x : α, p x → r :=
    λ hr : (∀ x : α, p x) → r ↦
    show ∃ x : α, p x → r from Classical.byContradiction $
    show (¬∃ x : α, p x → r) → False from
    sorry
  Iff.intro hlr hrl

example (α : Type) (p : α → Prop) (r : Prop) (a : α)
: (∃ x : α, r → p x) ↔ (r → ∃ x : α, p x) :=
  have hlr : (∃ x : α, r → p x) → r → ∃ x : α, p x := sorry
  have hrl : (r → ∃ x : α, p x) → ∃ x : α, r → p x := sorry
  Iff.intro hlr hrl

end TheExistentialQuantifier

section MoreOnTheProofLanguage
end MoreOnTheProofLanguage

section Exercises
end Exercises
