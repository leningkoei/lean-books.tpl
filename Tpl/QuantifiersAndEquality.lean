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
-- Will conflict with real `∣`
-- infix:50 " ∣ " => divides
-- example (h₁ : x ∣ y) (h₂ : y = z) : x ∣ (2 * z) := calc
--   x ∣ y       := h₁
--   _ = z       := h₂
--   _ ∣ (2 * z) := divides_mul ..

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

#check Classical.byCases
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
    -- show ∃ x : α, p x → r from
    --   have h : (∀ x : α, p x) → ∃ x : α, p x → r := λ h : ∀ x : α, p x ↦
    --   show ∃ x : α, p x → r from Exists.intro a $
    --   show p a → r from λ _hp : p a ↦
    --   show r from hr h
    --   have hn : (¬∀ x : α, p x) → ∃ x : α, p x → r := λ hn : ¬∀ x : α, p x ↦
    --     show ∃ x : α, p x → r from Classical.byContradiction $
    --     show (¬∃ x : α, p x → r) → False from λ hn' : ¬∃ x : α, p x → r ↦
    --     show False from
    --       have h : ∀ x : α, p x := λ w : α ↦
    --         show p w from Classical.byContradiction $
    --         show ¬p w → False from λ hnp : ¬p w ↦
    --         show False from hn' $
    --         show ∃ x : α, p x → r from Exists.intro w $
    --         show p w → r from λ hp : p w ↦
    --         show r from absurd hp hnp
    --     show False from hn h
    -- show ∃ x : α, p x → r from Classical.byCases h hn
    show ∃ x : α, p x → r from Classical.byContradiction $
    show (¬∃ x : α, p x → r) → False from λ hn : ¬∃ x : α, p x → r ↦
    show False from hn $
    show ∃ x : α, p x → r from Exists.intro a $
    show p a → r from λ _hp : p a ↦
    show r from hr $
    show ∀ x : α, p x from λ w : α ↦
    show p w from Classical.byContradiction $
    show ¬p w → False from λ hnp' : ¬p w ↦
    show False from hn $
    show ∃ x : α, p x → r from Exists.intro w $
    show p w → r from λ hp' : p w ↦
    show r from absurd hp' hnp'
  Iff.intro hlr hrl

example (α : Type) (p : α → Prop) (r : Prop) (a : α)
: (∃ x : α, r → p x) ↔ (r → ∃ x : α, p x) :=
  have hlr : (∃ x : α, r → p x) → r → ∃ x : α, p x :=
    λ hlr : ∃ x : α, r → p x ↦
    show r → ∃ x : α, p x from λ hr : r ↦
    show ∃ x : α, p x from Exists.elim hlr $
    show ∀ x : α, (r → p x) → ∃ x : α, p x from λ w : α ↦
    show (r → p w) → ∃ x : α, p x from λ h : r → p w ↦
    show ∃ x : α, p x from Exists.intro w $
    show p w from h $
    show r from hr
  have hrl : (r → ∃ x : α, p x) → ∃ x : α, r → p x :=
    λ hrl : r → ∃ x : α, p x ↦
    show ∃ x : α, r → p x from Classical.byContradiction $
    show (¬∃ x : α, r → p x) → False from λ hn : ¬∃ x : α, r → p x ↦
    show False from hn $
    show ∃ x : α, r → p x from Exists.intro a $
    show r → p a from λ hr : r ↦
    show p a from Classical.byContradiction $
    show ¬p a → False from λ _hnp : ¬p a ↦
    show False from hn $
    show ∃ x : α, r → p x from Exists.elim (hrl hr) $
    show ∀ x : α, p x → ∃ x : α, r → p x from λ w : α ↦
    show p w → ∃ x : α, r → p x from λ hp : p w ↦
    show ∃ x : α, r → p x from Exists.intro w $
    show r → p w from λ _hr : r ↦
    show p w from hp
  Iff.intro hlr hrl

example (α : Type) (a : α) (p : α → Prop) : (∃ x : α, p x) → p a :=
  λ h : ∃ x : α, p x ↦
  show p a from Exists.elim h $
  show ∀ x : α, p x → p a from
  sorry

end TheExistentialQuantifier

section MoreOnTheProofLanguage

#check Nat.le_trans
/--
# Anonymous `have` and `this`
Eliminating the clutter of lots of labels.
-/
example (f : Nat → Nat) (h : ∀ x : Nat, f x ≤ f (x + 1)) : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this $ h 1
  show f 0 ≤ f 3 from Nat.le_trans this $ h 2

/--
# Tactic: `assumption`
When the goal can be inferred, we can ask Lean instead to fill in the proof by
writing `by assumption`.
-/
example (f : Nat → Nat) (h : ∀ x : Nat, f x ≤ f (x + 1)) : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) $ h 1
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) $ h 2

#check Nat.le_antisymm
/--
# Notation: `‹p›`
Type `‹p›` by insert `\f<` `p` `\f>`.
Definition:
```lean4
notation "‹" p "›" => show p by assumption
```
-/
example (f : Nat → Nat) (h : ∀ x : Nat, f x ≤ f (x + 1))
: f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  λ _ : f 0 ≥ f 1 ↦
  λ _ : f 1 ≥ f 2 ↦
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 2 ≥ f 0 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›

end MoreOnTheProofLanguage

section Exercises
/-!
1. Prove these equivalences:
You should also try to understand why the reverse implication is not derivable
in the last example.
-/
section paragraph

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  have hlr : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) :=
    λ h : ∀ x, p x ∧ q x ↦
    have hp : ∀ x, p x := λ w : α ↦
      have hpq : p w ∧ q w := h w
      show p w from hpq.left
    have hq : ∀ x, q x := λ w : α ↦
      have hpq : p w ∧ q w := h w
      show q w from hpq.right
    show (∀ x, p x) ∧ (∀ x, q x) from And.intro hp hq
  have hrl : (∀ x, p x) ∧ (∀ x, q x) → ∀ x, p x ∧ q x :=
    λ h : (∀ x, p x) ∧ (∀ x, q x) ↦
    show ∀ x, p x ∧ q x from λ w : α ↦
    show p w ∧ q w from
      have hp : p w :=
        show p w from
          have : ∀ x, p x := h.left
          have : (x : α) → p x := this
        show p w from this w
      have hq : q w :=
        show q w from
          have : ∀ x, q x := h.right
          have : (x : α) → q x := this
        show q w from this w
    show p w ∧ q w from And.intro hp hq
  Iff.intro hlr hrl

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  λ h₁ : ∀ x, p x → q x ↦
  λ h₂ : ∀ x, p x ↦
  show ∀ x, q x from λ w : α ↦
  show q w from
    have : (x : α) → p x := h₂
    have hp : p w := this w
    have : (x : α) → p x → q x := h₁
    have hq : q w := this w hp
  show q w from hq

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ h : (∀ x, p x) ∨ (∀ x, q x) ↦
  show ∀ x, p x ∨ q x from
    have hleft : (∀ x, p x) → ∀ x, p x ∨ q x :=
      λ h : ∀ x, p x ↦
      show ∀ x, p x ∨ q x from λ w : α ↦
      show p w ∨ q w from
        have : (x : α) → p x := h
        have : p w := this w
      show p w ∨ q w from Or.inl this
    have hright : (∀ x, q x) → ∀ x, p x ∨ q x :=
      λ h : ∀ x, q x ↦
      show ∀ x, p x ∨ q x from λ w : α ↦
      show p w ∨ q w from
        have : (x : α) → q x := h
        have : q w := this w
      show p w ∨ q w from Or.inr this
  show ∀ x, p x ∨ q x from Or.elim h hleft hright

example
: ∃ (α : Type) (p q : α → Prop),
  ((∀ x, p x ∨ q x) → (∀ x, p x) ∨ (∀ x, q x)) → False :=
  let hα := Bool
  let hp := λ x => x = true
  let hq := λ x => x = false
  Exists.intro hα $
  Exists.intro hp $
  Exists.intro hq $
  show ((∀ x, hp x ∨ hq x) → (∀ x, hp x) ∨ (∀ x, hq x)) → False
  from λ h : (∀ x, hp x ∨ hq x) → (∀ x, hp x) ∨ (∀ x, hq x) =>
  show False from
    have hn : ((∀ x, hp x) ∨ (∀ x, hq x)) → False :=
      λ h : (∀ x, hp x) ∨ (∀ x, hq x) =>
      show False from
        have h₁ : (∀ x, hp x) → False := λ h : ∀ x, hp x =>
          have : hp false := h false
          have : false = true := this
          have : False := Bool.false_ne_true this
          show False from this
        have h₂ : (∀ x, hq x) → False := λ h : ∀ x, hq x =>
          show False from Bool.false_ne_true $
          show false = true from Eq.symm $
          show true = false from
          show hq true from
            have : (x : Bool) → hq x := h
          show hq true from this true
      show False from Or.elim h h₁ h₂
    have h : (∀ x, hp x) ∨ (∀ x, hq x) := h $
      show ∀ x, hp x ∨ hq x from λ
      | true =>
        show hp true ∨ hq true from
        show true = true ∨ true = false from Or.inl $
        show true = true from Eq.refl true
      | false =>
        show hp false ∨ hq false from
        show false = true ∨ false = false from Or.inr $
        show false = false from Eq.refl false
  show False from hn h

end paragraph

/-!
2. It is often possible to bring a component of a formula outside a universal
quantifier, when it does not depend on the quantified variable. Try proving
these (one direction of the second of these requires classical logic):
-/
section paragraph

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _x : α, r) ↔ r) := λ w : α =>
  show (∀ _x, r) ↔ r from
    have hlr : (∀ _x, r) → r := λ h : ∀ _x, r =>
      show r from
        have : (x : α) → r := h
      show r from this w
    have hrl : r → ∀ _x, r := λ hr : r =>
      show ∀ _x, r from λ _v : α =>
      show r from hr
  show (∀ _x, r) ↔ r from Iff.intro hlr hrl

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  have hlr : (∀ x, p x ∨ r) → (∀ x, p x) ∨ r := λ h : ∀ x, p x ∨ r =>
    show (∀ x, p x) ∨ r from Classical.byContradiction $
    show ((∀ x, p x) ∨ r → False) → False from λ h' : (∀ x, p x) ∨ r → False =>
    show False from h' $
    show (∀ x, p x) ∨ r from Or.inl $
    show ∀ x, p x from λ w : α =>
    show p w from
      have : (x : α) → p x ∨ r := h
      have : p w ∨ r := this w
    show p w from
      have h₁ : p w → p w := λ hp : p w =>
        show p w from hp
      have h₂ : r → p w := λ hr : r =>
        show p w from
          have h : (∀ x, p x) ∨ r := Or.inr hr
        show p w from absurd h h'
    show p w from Or.elim this h₁ h₂
  have hrl : (∀ x, p x) ∨ r → ∀ x, p x ∨ r := λ h : (∀ x, p x) ∨ r =>
    show ∀ x, p x ∨ r from
      have h₁ : (∀ x, p x) → ∀ x, p x ∨ r := λ h : ∀ x, p x =>
        show ∀ x, p x ∨ r from λ w : α =>
        show p w ∨ r from Or.inl $
        show p w from
          have : (x : α) → p x := h
        show p w from this w
      have h₂ : r → ∀ x, p x ∨ r := λ hr : r =>
        show ∀ x, p x ∨ r from λ w : α =>
        show p w ∨ r from Or.inr $
        show r from hr
    show ∀ x, p x ∨ r from Or.elim h h₁ h₂
  Iff.intro hlr hrl

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  have hlr : (∀ x, r → p x) → (r → ∀ x, p x) := λ h : ∀ x, r → p x =>
    show r → ∀ x, p x from λ hr : r =>
    show ∀ x, p x from λ w : α =>
    show p w from
      have : (x : α) → r → p x := h
      have : r → p w := this w
      have : p w := this hr
    show p w from this
  have hrl : (r → ∀ x, p x) → (∀ x, r → p x) := λ h : r → ∀ x, p x =>
    show ∀ x, r → p x from λ w : α =>
    show r → p w from λ hr : r =>
    show p w from
      have : ∀ x, p x := h hr
      have : (x : α) → p x := this
      have : p w := this w
    show p w from this
  Iff.intro hlr hrl

end paragraph

/-!
3. Consider the "barber paradox", that is, the claim that in a certain town
there is a (male) barber that shaves all and only the men who do not shave
themselves. Prove that this is a contradiction:
-/
section paragraph

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

#check Iff.elim
example (h : ∀ x : men, shaves barber x ↔ ¬shaves x x) : False :=
  have : shaves barber barber ↔ ¬shaves barber barber := h barber
  show False from Iff.elim (
    show (shaves barber barber → ¬shaves barber barber) → (¬shaves barber barber
      → shaves barber barber) → False
    from
      λ hlr : shaves barber barber → ¬shaves barber barber =>
      λ hrl : ¬shaves barber barber → shaves barber barber =>
    show False from
      have h₁ : shaves barber barber → False := λ h₁ : shaves barber barber =>
        show False from hlr h₁ $ h₁
      have h₂ : ¬shaves barber barber → False := λ h₂ : ¬shaves barber barber =>
        show False from h₂ $ hrl h₂
    show False from Classical.byCases h₁ h₂
  ) this

end paragraph
/-!
4. Remember that, without any parameters, an expression of type `Prop` is just
an assertion. Fill in the definitions of `prime` and `Fermat_prime` below, and
construct each of the given assertions. For example, you can say that there are
infinitely many primes by asserting that for every natural number `n`, there is
a prime number greater than `n`. Goldbach's weak conjecture states that every
odd number greater than 5 is the sum of three primes. Look up the definition of
a Fermat prime or any of the other statements, if necessary.
-/
section paragraph

def even (n : Nat) : Prop :=
  sorry

def prime (n : Nat) : Prop :=
  sorry

def infinitely_many_primes : Prop :=
  sorry

def Fermat_prime (n : Nat) : Prop :=
  sorry

def infinitely_many_Fermat_primes : Prop :=
  sorry

def goldbach_conjecture : Prop :=
  sorry

def Goldbach's_weak_conjecture : Prop :=
  sorry

def Fermat's_last_theorem : Prop :=
  sorry

end paragraph

end Exercises
