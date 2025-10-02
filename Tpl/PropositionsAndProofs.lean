section PropositionsAsTypes

#check And
#check Or
#check Not
def Implies : Prop → Prop → Prop := sorry
#check Implies
def Proof : Prop → Type := sorry
#check Proof

axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)

end PropositionsAsTypes

section WorkingWithPropositionsAsTypes

variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := λ hp : p ↦ λ hq : q ↦ show p from hp
#print t1

variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  λ h₃ : p ↦
    h₁ (h₂ h₃)

#print False.elim

end WorkingWithPropositionsAsTypes

section PropositionalLogic

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

section Conjunction

variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
#check λ (hp : p) (hq : q) ↦ And.intro hp hq
#check And.intro

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)

example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

example (h : p ∧ q) : q ∧ p ∧ q := ⟨h.right, h.left, h.right⟩

end Conjunction

section Disjunction

variable (p q : Prop)

example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

example (h : p ∨ q) : q ∨ p := Or.elim h
  (λ hp : p ↦ show q ∨ p from Or.intro_right q hp)
  (λ hq : q ↦ show q ∨ p from Or.intro_left p hq)

example (h : p ∨ q) : q ∨ p := h.elim
  (λ hp : p ↦ show q ∨ p from Or.inr hp)
  (λ hq : q ↦ show q ∨ p from Or.inl hq)

end Disjunction

section NegationAndFalsity

variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  λ hp : p ↦ show False from hnq (hpq hp)

end NegationAndFalsity

section LogicalEquivalence

variable (p q : Prop)

#check Iff.intro
theorem and_swap : p ∧ q ↔ q ∧ p := Iff.intro
  (λ h : p ∧ q ↦ show q ∧ p from ⟨h.right, h.left⟩)
  (λ h : q ∧ p ↦ show p ∧ q from ⟨h.right, h.left⟩)
#check Iff.mp
example (h : p ∧ q) : q ∧ p := Iff.mp (and_swap p q) h

theorem and_swap' : p ∧ q ↔ q ∧ p :=
  ⟨ λ h : p ∧ q ↦ show q ∧ p from ⟨h.right, h.left⟩
  , λ h : q ∧ p ↦ show p ∧ q from ⟨h.right, h.left⟩ ⟩
example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

end LogicalEquivalence

end PropositionalLogic

section IntroducingAuxiliarySubgoals

variable (p q : Prop)
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from ⟨hq, hp⟩
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from ⟨hq, hp⟩
  show q from h.right

end IntroducingAuxiliarySubgoals

section ClassicalLogic

open Classical

variable (p : Prop)
#check em p

#check absurd
#check False
theorem dne {p : Prop} (h : ¬¬p) : p := Or.elim (em p)
  (λ hp : p ↦ show p from hp)
  -- (λ hnp : ¬p ↦ show p from absurd hnp h)
  (λ hnp : ¬p ↦ show p from False.elim (h hnp))

theorem em' (p : Prop) : p ∨ ¬p := by
  apply dne
  intro h
  have hnp : ¬p := λ hp : p ↦ h (Or.intro_left (¬p) hp)
  exact h (Or.intro_right p hnp)
theorem em'' (p : Prop) : p ∨ ¬p :=
  have h' : ¬(p ∨ ¬p) → False := λ h : ¬(p ∨ ¬p) ↦ show False from
    have hnp : ¬p := show p → False from λ hp : p ↦ h (Or.intro_left (¬p) hp)
    have h' : p ∨ ¬p := Or.intro_right p hnp
    h h'
  have h : ¬¬(p ∨ ¬p) := h'
  dne h
theorem em''' (p : Prop) : p ∨ ¬p := dne $
  show ¬¬(p ∨ ¬p) from
  show ¬(p ∨ ¬p) → False from λ h : ¬(p ∨ ¬p) ↦
  show False from h $
  show (p ∨ ¬p) from Or.intro_right p $
  show ¬p from
  show p → False from λ hp : p ↦
  show False from h $
  show (p ∨ ¬p) from Or.intro_left (¬p) hp

#check byCases
example {p : Prop} (h : ¬¬p) : p := show p from byCases
  (show p → p from λ h1 : p ↦ show p from h1)
  (show ¬p → p from λ h1 : ¬p ↦ show p from absurd h1 h)

#check byContradiction
example {p : Prop} (h : ¬¬p) : p := show p from byContradiction $
  show ¬p → False from λ hnp : ¬p ↦
  show False from h hnp

example {p q : Prop} (h : ¬(p ∧ q)) : ¬p ∨ ¬q := Or.elim (em p)
  ( show p → ¬p ∨ ¬q from λ hp : p ↦
    show ¬p ∨ ¬q from Or.inr $
    show ¬q from
    show q → False from λ hq : q ↦
    show False from h ⟨hp, hq⟩ )
  (show ¬p → ¬p ∨ ¬q from λ hnp : ¬p ↦ show ¬p ∨ ¬q from Or.inl hnp)

-- distributivity
example {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := Iff.intro
  ( show p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) from λ h : p ∧ (q ∨ r) ↦
    have hp : p := h.left
    show (p ∧ q) ∨ (p ∧ r) from Or.elim h.right
      ( show q → (p ∧ q) ∨ (p ∧ r) from λ hq : q ↦
        show (p ∧ q) ∨ (p ∧ r) from Or.inl $
        show p ∧ q from ⟨hp, hq⟩ )
      ( show r → (p ∧ q) ∨ (p ∧ r) from λ hr : r ↦
        show (p ∧ q) ∨ (p ∧ r) from Or.inr $
        show p ∧ r from ⟨hp, hr⟩ ) )
  ( show (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) from λ h : (p ∧ q) ∨ (p ∧ r) ↦
    show p ∧ (q ∨ r) from Or.elim h
      ( show p ∧ q → p ∧ (q ∨ r) from λ h : p ∧ q ↦
        have hp : p := h.left
        have hq : q := h.right
        show p ∧ (q ∨ r) from ⟨hp,
        show q ∨ r from Or.inl hq⟩ )
      ( show p ∧ r → p ∧ (q ∨ r) from λ h : p ∧ r ↦
        have hp : p := h.left
        have hr : r := h.right
        show p ∧ (q ∨ r) from ⟨hp,
        show q ∨ r from Or.inr hr⟩ ) )

example {p q : Prop} : ¬(p ∧ ¬q) → (p → q) := λ h : ¬(p ∧ ¬q) ↦
  show p → q from λ hp : p ↦
  show q from Or.elim (em q)
    (show q → q from λ hq : q ↦ hq)
    ( show ¬q → q from λ hnq : ¬q ↦
      have h' : p ∧ ¬q := ⟨hp, hnq⟩
      show q from absurd h' h )

end ClassicalLogic

section Exercises

section part1
/-!
Prove the following identities, replacing the `sorry` placeholders with actual
proofs.
-/

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := Iff.intro
  (show p ∧ q → q ∧ p from λ h : p ∧ q ↦ show q ∧ p from ⟨h.right, h.left⟩)
  (show q ∧ p → p ∧ q from λ h : q ∧ p ↦ show p ∧ q from ⟨h.right, h.left⟩)
example : p ∨ q ↔ q ∨ p := Iff.intro
  ( show p ∨ q → q ∨ p from λ h : p ∨ q ↦
    show q ∨ p from Or.elim h
      (show p → q ∨ p from λ hp : p ↦ show q ∨ p from Or.inr hp)
      (show q → q ∨ p from λ hq : q ↦ show q ∨ p from Or.inl hq) )
  ( show q ∨ p → p ∨ q from λ h : q ∨ p ↦
    show p ∨ q from Or.elim h
      (show q → p ∨ q from λ hq : q ↦ show p ∨ q from Or.inr hq)
      (show p → p ∨ q from λ hp : p ↦ show p ∨ q from Or.inl hp) )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := Iff.intro
  ( show (p ∧ q) ∧ r → p ∧ (q ∧ r) from λ h : (p ∧ q) ∧ r ↦
    have hp : p := h.left.left
    have hq : q := h.left.right
    have hr : r := h.right
    show p ∧ (q ∧ r) from ⟨hp, ⟨hq, hr⟩⟩ )
  ( show p ∧ (q ∧ r) → (p ∧ q) ∧ r from λ h : p ∧ (q ∧ r) ↦
    have hp : p := h.left
    have hq : q := h.right.left
    have hr : r := h.right.right
    show (p ∧ q) ∧ r from ⟨⟨hp, hq⟩, hr⟩ )
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := Iff.intro
  ( show (p ∨ q) ∨ r → p ∨ (q ∨ r) from λ h : (p ∨ q) ∨ r ↦
    show p ∨ (q ∨ r) from Or.elim h
      ( show p ∨ q → p ∨ (q ∨ r) from λ h' : p ∨ q ↦
        show p ∨ (q ∨ r) from Or.elim h'
        ( show p → p ∨ (q ∨ r) from λ hp : p ↦
          show p ∨ (q ∨ r) from Or.inl hp )
        ( show q → p ∨ (q ∨ r) from λ hq : q ↦
          show p ∨ (q ∨ r) from Or.inr ∘ Or.inl $ hq ) )
      ( show r → p ∨ (q ∨ r) from λ hr : r ↦
        show p ∨ (q ∨ r) from Or.inr ∘ Or.inr $ hr ) )
  ( show p ∨ (q ∨ r) → (p ∨ q) ∨ r from λ h : p ∨ (q ∨ r) ↦
    show (p ∨ q) ∨ r from Or.elim h
      ( show p → (p ∨ q) ∨ r from λ hp : p ↦
        show (p ∨ q) ∨ r from Or.inl ∘ Or.inl $ hp )
      ( show q ∨ r → (p ∨ q) ∨ r from λ h' : q ∨ r ↦
        show (p ∨ q) ∨ r from Or.elim h'
        ( show q → (p ∨ q) ∨ r from λ hq : q ↦
          show (p ∨ q) ∨ r from Or.inl ∘ Or.inr $ hq )
        ( show r → (p ∨ q) ∨ r from λ hr : r ↦
          show (p ∨ q) ∨ r from Or.inr hr ) ) )

-- distributitiy
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := Iff.intro
  ( show p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) from λ h : p ∧ (q ∨ r) ↦
    have hp : p := h.left
    show (p ∧ q) ∨ (p ∧ r) from Or.elim h.right
      ( show q → (p ∧ q) ∨ (p ∧ r) from λ hq : q ↦
        show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩ )
      ( show r → (p ∧ q) ∨ (p ∧ r) from λ hr : r ↦
        show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩ ) )
  ( show (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) from λ h : (p ∧ q) ∨ (p ∧ r) ↦
    show p ∧ (q ∨ r) from Or.elim h
      ( show p ∧ q → p ∧ (q ∨ r) from λ h' : p ∧ q ↦
        have hp : p := h'.left
        have hq : q := h'.right
        show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩ )
      ( show p ∧ r → p ∧ (q ∨ r) from λ h' : p ∧ r ↦
        have hp : p := h'.left
        have hr : r := h'.right
        show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩ ) )
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := Iff.intro
  ( show p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) from λ h : p ∨ (q ∧ r) ↦
    show (p ∨ q) ∧ (p ∨ r) from Or.elim h
      ( show p → (p ∨ q) ∧ (p ∨ r) from λ hp : p ↦
        show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inl hp, Or.inl hp⟩ )
      ( show q ∧ r → (p ∨ q) ∧ (p ∨ r) from λ h' : q ∧ r ↦
        have hq : q := h'.left
        have hr : r := h'.right
        show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inr hq, Or.inr hr⟩ ) )
  ( show (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) from λ h : (p ∨ q) ∧ (p ∨ r) ↦
    have h1 : p ∨ q := h.left
    have h2 : p ∨ r := h.right
    show p ∨ (q ∧ r) from Or.elim h1
      ( show p → p ∨ (q ∧ r) from λ hp : p ↦
        show p ∨ (q ∧ r) from Or.inl hp )
      ( show q → p ∨ (q ∧ r) from λ hq : q ↦
        show p ∨ (q ∧ r) from Or.elim h2
          ( show p → p ∨ (q ∧ r) from λ hp : p ↦
            show p ∨ (q ∧ r) from Or.inl hp )
          ( show r → p ∨ (q ∧ r) from λ hr : r ↦
            show p ∨ (q ∧ r) from Or.inr ⟨hq, hr⟩ ) ) )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := Iff.intro
  ( show (p → (q → r)) → (p ∧ q → r) from λ h : p → (q → r) ↦
    show p ∧ q → r from λ h' : p ∧ q ↦
    have hp : p := h'.left
    have hq : q := h'.right
    have hq2r : q → r := h hp
    have hr : r := hq2r hq
    show r from hr )
  ( show (p ∧ q → r) → (p → (q → r)) from λ h : p ∧ q → r ↦
    show p → (q → r) from λ hp : p ↦
    show q → r from λ hq : q ↦
    have h' : p ∧ q := ⟨hp, hq⟩
    show r from h h' )
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := Iff.intro
  ( show ((p ∨ q) → r) → (p → r) ∧ (q → r) from λ h : (p ∨ q) → r ↦
    have hp2r : p → r := λ hp : p ↦
      show r from h ∘ Or.inl $ hp
    have hq2r : q → r := λ hq : q ↦
      show r from h ∘ Or.inr $ hq
    show (p → r) ∧ (q → r) from ⟨hp2r, hq2r⟩ )
  ( show (p → r) ∧ (q → r) → ((p ∨ q) → r) from λ h : (p → r) ∧ (q → r) ↦
    have hp2r : p → r := h.left
    have hq2r : q → r := h.right
    show (p ∨ q) → r from λ h' : p ∨ q ↦
    show r from Or.elim h'
      ( show p → r from λ hp : p ↦
        show r from hp2r hp )
      ( show q → r from λ hq : q ↦
        show r from hq2r hq ) )
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := Iff.intro
  ( show ¬(p ∨ q) → ¬p ∧ ¬q from λ h : ¬(p ∨ q) ↦
    have hnp : ¬p := show p → False from λ hp : p ↦
      show False from h $ Or.inl hp
    have hnq : ¬q := show q → False from λ hq : q ↦
      show False from h $ Or.inr hq
    show ¬p ∧ ¬q from ⟨hnp, hnq⟩)
  ( show ¬p ∧ ¬q → ¬(p ∨ q) from λ h : ¬p ∧ ¬q ↦
    have hnp : ¬p := h.left
    have hnq : ¬q := h.right
    show ¬(p ∨ q) from
    show p ∨ q → False from λ h' : p ∨ q ↦
    show False from Or.elim h'
      ( show p → False from λ hp : p ↦ show False from hnp hp )
      ( show q → False from λ hq : q ↦ show False from hnq hq ) )
example : ¬p ∨ ¬q → ¬(p ∧ q) := λ h : ¬p ∨ ¬q ↦
  show ¬(p ∧ q) from
  show p ∧ q → False from λ h' : p ∧ q ↦
  have hp : p := h'.left
  have hq : q := h'.right
  show False from Or.elim h
    ( show ¬p → False from λ hnp : ¬p ↦ hnp hp )
    ( show ¬q → False from λ hnq : ¬q ↦ hnq hq )
example : ¬(p ∧ ¬p) :=
  show p ∧ ¬p → False from λ h : p ∧ ¬p ↦
  have hp : p := h.left
  have hnp : ¬p := h.right
  show False from hnp hp
example : p ∧ ¬q → ¬(p → q) := λ h : p ∧ ¬q ↦
  show ¬(p → q) from
  show (p → q) → False from λ h' : p → q ↦
  have hp : p := h.left
  have hnq : ¬q := h.right
  have hq : q := h' hp
  show False from hnq hq
example : ¬p → (p → q) := λ hnp : ¬p ↦
  show p → q from λ hp : p ↦
  show q from absurd hp hnp
example : (¬p ∨ q) → (p → q) := λ h : ¬p ∨ q ↦
  show p → q from λ hp : p ↦
  show q from Or.elim h
    ( show ¬p → q from λ hnp : ¬p ↦
      show q from absurd hp hnp )
    ( show q → q from λ hq : q ↦ hq )
example : p ∨ False ↔ p := Iff.intro
  ( show p ∨ False → p from λ h : p ∨ False ↦
    show p from h.elim
      ( show p → p from λ hp : p ↦ hp )
      ( show False → p from λ f : False ↦ f.elim ) )
  ( show p → p ∨ False from λ hp : p ↦
    show p ∨ False from Or.inl hp )
example : p ∧ False ↔ False := Iff.intro
  ( show p ∧ False → False from λ h : p ∧ False ↦ show False from h.right )
  ( show False → p ∧ False from λ f : False ↦ show p ∧ False from f.elim )
example : (p → q) → (¬q → ¬p) := λ h : p → q ↦
  show ¬q → ¬p from λ hnq : ¬q ↦
  show ¬p from
  show p → False from λ hp : p ↦
  have hq : q := h hp
  show False from hnq hq

end part1

section part2
/-!
Prove the following identities, replacing the `sorry` placeholders with actual
proofs. These require classical reasoning.
-/

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := λ h : p → q ∨ r ↦
  show (p → q) ∨ (p → r) from Or.elim (em (p → q))
    ( show (p → q) → (p → q) ∨ (p → r) from λ h' : p → q ↦
      show (p → q) ∨ (p → r) from Or.inl h' )
    ( show ¬(p → q) → (p → q) ∨ (p → r) from λ h' : ¬(p → q) ↦
      have hp2r : p → r := λ hp : p ↦
        show r from (h hp).elim
          ( show q → r from λ hq : q ↦
            have h : p → q := λ _hp : p ↦ show q from hq
            show r from absurd h h')
          ( show r → r from λ hr : r ↦ show r from hr )
      show (p → q) ∨ (p → r) from Or.inr hp2r )
example : ¬(p ∧ q) → ¬p ∨ ¬q := λ h : ¬(p ∧ q) ↦
  show ¬p ∨ ¬q from (em p).elim
    ( show p → ¬p ∨ ¬q from λ hp : p ↦
      have hnq : ¬q :=
        show q → False from λ hq : q ↦
        have h' : p ∧ q := ⟨hp, hq⟩
        show False from h h'
      show ¬p ∨ ¬q from Or.inr hnq )
    ( show ¬p → ¬p ∨ ¬q from λ hnp : ¬p ↦
      show ¬p ∨ ¬q from Or.inl hnp )
example : ¬(p → q) → p ∧ ¬q := λ h : ¬(p → q) ↦
  show p ∧ ¬q from (em p).elim
    ( show p → p ∧ ¬q from λ hp : p ↦
      have hnq : ¬q :=
        show q → False from λ hq : q ↦
        have h' : p → q := λ _hp : p ↦ show q from hq
        show False from h h'
      show p ∧ ¬q from ⟨hp, hnq⟩ )
    ( show ¬p → p ∧ ¬q from λ hnp : ¬p ↦
      have hp2q : p → q := λ hp : p ↦
        show q from absurd hp hnp
      show p ∧ ¬q from absurd hp2q h )
example : (p → q) → (¬p ∨ q) := λ h : p → q ↦
  show ¬p ∨ q from (em p).elim
    ( show p → ¬p ∨ q from λ hp : p ↦
      show ¬p ∨ q from Or.inr $ h hp )
    ( show ¬p → ¬p ∨ q from λ hnp : ¬p ↦ show ¬p ∨ q from Or.inl hnp )
example : (¬q → ¬p) → (p → q) := λ h : (¬q → ¬p) ↦
  show p → q from λ hp : p ↦
  show q from (em q).elim
    ( show q → q from λ hq : q ↦ show q from hq )
    ( show ¬q → q from λ hnq : ¬q ↦
      have hnp : ¬p := h hnq
      show q from absurd hp hnp )
example : p ∨ ¬p := (em p).elim
  (show p → p ∨ ¬p from λ hp : p ↦ show p ∨ ¬p from Or.inl hp)
  (show ¬p → p ∨ ¬p from λ hnp : ¬p ↦ show p ∨ ¬p from Or.inr hnp)
example : (((p → q) → p) → p) := λ h : (p → q) → p ↦
  show p from (em p).elim
    ( show p → p from λ hp : p ↦ show p from hp )
    ( show ¬p → p from λ hnp : ¬p ↦
      have h' : p → q := λ hp : p ↦ show q from absurd hp hnp
      show p from h h' )

end part2

section part3
/-!
Prove `¬(p ↔ ¬p)` without using classical logic.
-/

variable (p : Prop)

example : ¬(p ↔ ¬p) :=
  show (p ↔ ¬p) → False from λ h : p ↔ ¬p ↦
  show False from h.elim $
  show (p → ¬p) → (¬p → p) → False from λ h1 : p → ¬p ↦
  show (¬p → p) → False from λ h2 : ¬p → p ↦
  have hnp : ¬p :=
    show p → False from λ hp ↦
    show False from (h1 hp) hp
  have hp : p := h2 hnp
  show False from hnp hp

open Classical in
example : ¬(p ↔ ¬p) :=
  show (p ↔ ¬p) → False from λ h : p ↔ ¬p ↦
  show False from h.elim $
  show (p → ¬p) → (¬p → p) → False from λ h1 : p → ¬p ↦
  show (¬p → p) → False from λ h2 : ¬p → p ↦
  show False from Or.elim (em p)
    ( show p → False from λ hp : p ↦
      have hnp : ¬p := h1 hp
      show False from hnp hp )
    ( show ¬p → False from λ hnp : ¬p ↦
      have hp : p := h2 hnp
      show False from hnp hp )

end part3

end Exercises
