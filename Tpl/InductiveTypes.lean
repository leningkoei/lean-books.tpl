/-!
# Chapter 7. Inductive Types
-/

/-!
## Section 7.1. EnumeratedTypes
-/
section EnumeratedTypes

inductive Weekday where
| sunday
| monday
| tuesday
| wednesday : Weekday -- No necessary to declare the type.
| thursday
| friday
| saturday
deriving Repr

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | .sunday => 1
  | .monday => 2
  | .tuesday => 3
  | .wednesday => 4
  | .thursday => 5
  | .friday => 6
  | .saturday => 7

namespace Weekday

def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday
def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

example : tuesday = previous (next tuesday) := by
  rw [next]
  rw [previous]

theorem next_previous (d : Weekday) : d.previous.next = d := by
  cases d <;>
  rw [previous] <;>
  rw [next]

end Weekday

namespace Hidden

inductive Bool where
| false : Bool
| true : Bool

def Bool.and : Bool → Bool → Bool
| .true, .true => .true
| _, _ => .false

def Bool.or : Bool → Bool → Bool
| .false, .false => .false
| _, _ => .true

def Bool.not : Bool → Bool
| .true => .false
| .false => .true

def Bool.not_true_eq_false : Bool.not Bool.true = Bool.false := by
  rw [Bool.not]
def Bool.not_false_eq_true : Bool.not Bool.false = Bool.true := by
  rw [Bool.not]

end Hidden

end EnumeratedTypes

/-!
## Section 7.2. Constructor with Arguments
-/
section ConstructorWithArguments

namespace Hidden

inductive Prod (α : Type u) (β : Type v)
| mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v)
| inl : α → Sum α β
| inr : β → Sum α β

def Prod.fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a _b => a
def Prod.snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk _a b => b

#check cond
def Bool.cond : Bool → α → α → α
| .true, a, _ => a
| .false, _, b => b

#check @Prod.casesOn
def prod_example (p : Prod Bool Nat) : Nat :=
  Prod.casesOn (motive := λ _ : Prod Bool Nat ↦ Nat) p
    (λ (b : Bool) (n : Nat) ↦ Bool.cond b (2 * n) (2 * n + 1))
#eval prod_example $ Prod.mk .true 3
#eval prod_example $ Prod.mk .false 3

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := λ _ ↦ Nat) s
    (λ n ↦ 2 * n)
    (λ n ↦ 2 * n + 1)
#eval sum_example $ Sum.inl 3
#eval sum_example $ Sum.inr 3

end Hidden
end ConstructorWithArguments

/-!
## Section 7.3. Inductively Defined Propositions
-/
section InductivelyDefinedPropositions

#print Empty
#print PUnit
#print Sigma

namespace Hidden

inductive False : Prop
inductive Empty : Type u

inductive True : Prop
| intro
inductive Unit : Type u
| mk

inductive And (a b : Prop) : Prop
| intro : a → b → And a b

inductive Or (a b : Prop) : Prop
| inl : a → Or a b
| inr : b → Or a b

inductive Exists {α : Sort u} (p : α → Prop) : Prop
| intro (w : α) (h : p w) : Exists p
inductive Sigma {α : Type u} (β : α → Type v) : Type (max u v)
| mk (fst : α) (snd : β fst) : Sigma β
inductive Subtype {α : Type u} (p : α → Prop)
| mk : (x : α) → p x → Subtype p
def PositiveInteger : Type := Subtype (λ x : Nat ↦ x > 0)
def one : PositiveInteger := Subtype.mk 1
  (show 1 > 0 by simp)

end Hidden

end InductivelyDefinedPropositions

/-!
## Section 7.4. Defining the Natural Numbers
-/
section DefiningTheNaturalNumbers

namespace Hidden

inductive Nat
| zero : Nat
| succ : Nat → Nat
deriving Repr

namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | .zero => m
  | .succ n' => .succ $ add m n'
#eval add (succ (succ zero)) (succ zero)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := by
  show add m zero = m
  rw [add]
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := by
  show add m n.succ = (add m n).succ
  rw [add]
#check @Nat.recOn
theorem zero_add (n : Nat) : zero + n = n :=
  Nat.recOn (motive := λ x ↦ zero + x = x) n
    (show zero + zero = zero by rw [add_zero])
    ( show (n' : Nat) → zero + n' = n' → zero + n'.succ = n'.succ by
      intro n'
      intro h
      show add zero n'.succ = n'.succ
      rw [add]
      simp
      show zero + n' = n'
      rw [h] )
theorem zero_add' (n : Nat) : zero + n = n :=
  Nat.recOn (motive := λ x ↦ zero + x = x) n
    rfl
    (λ n ih ↦ by simp [add_succ, ih])

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := λ k => m + n + k = m + (n + k)) k
    (show m + n + zero = m + (n + zero) from rfl)
    ( show (k' : Nat) → m + n + k' = m + (n + k') →
        m + n + k'.succ = m + (n + k'.succ) from
        λ k' : Nat ↦ -- show m + n + k' = m + (n + k') → m + n + k'.succ = m + (n + k'.succ) from
        λ h : m + n + k' = m + (n + k') ↦ -- show m + n + k'.succ = m + (n + k'.succ) from
      calc  m + n + k'.succ
        _ = (m + n + k').succ   := by rw [add_succ (m + n) k']
        _ = (m + (n + k')).succ := by rw [h]
        _ = m + (n + k').succ   := by rw [add_succ m (n + k')]
        _ = m + (n + k'.succ)   := by rw [add_succ n k']
    )

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) :=
  Nat.recOn (motive := λ n ↦ succ m + n = succ (m + n)) n
    (show succ m + zero = succ (m + zero) by repeat rw [add_zero])
    ( show (n' : Nat) → succ m + n' = succ (m + n') →
        succ m + n'.succ = succ (m + n'.succ) by
      intro n' h
      repeat rw [add_succ]
      rw [h] )

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := λ m ↦ m + n = n + m) m
    ( show zero + n = n + zero from
      Nat.recOn (motive := λ n ↦ zero + n = n + zero) n
        (show zero + zero = zero + zero by simp)
        ( show (n' : Nat) → zero + n' = n' + zero →
            zero + n'.succ = n'.succ + zero by
          intro n' h
          rw [zero_add, add_zero] ) )
    ( show (m' : Nat) → m' + n = n + m' → m'.succ + n = n + m'.succ from
      λ m' h ↦
      Nat.recOn (motive := λ n ↦ m'.succ + n = n + m'.succ) n
        (show m'.succ + zero = zero + m'.succ by rw [add_zero, zero_add])
        ( show (n' : Nat) → m'.succ + n' = n' + m'.succ →
            m'.succ + n'.succ = n'.succ + m'.succ by
          intro n' h'
          rw [add_succ]
          rw [succ_add n' m'.succ]
          rw [h'] ) )

end Nat

end Hidden

end DefiningTheNaturalNumbers

/-!
## Section 7.5. Other Recursive Data Types
-/
section OtherRecursiveDataTypes

namespace Hidden

inductive List (α : Type u)
| nil : List α
| cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil => bs
  | cons a as' => cons a $ as'.append bs

theorem nil_append (as : List α) : append nil as = as := by
  rw [append]
theorem cons_append (a : α) (as bs : List α)
: append (cons a as) bs = cons a (append as bs) := by
  rw [append]

#check @List.recOn
theorem append_nil (as : List α) : append as nil = as :=
  List.recOn (motive := λ as ↦ append as nil = as) as
    (show append nil nil = nil by apply nil_append)
    ( show (a : α) → (as' : List α) → append as' nil = as' →
        append (cons a as') nil = (cons a as') by
      intro a as' h
      rw [append]
      simp
      exact h )

theorem append_assoc (as bs cs : List α)
: append (append as bs) cs = append as (append bs cs) :=
  List.recOn
    (motive := λ as ↦ append (append as bs) cs = append as (append bs cs))
    as
    ( show append (append nil bs) cs = append nil (append bs cs) by
      repeat rw [nil_append] )
    ( show (a : α) → (as' : List α) →
        append (append as' bs) cs = append as' (append bs cs) →
        append (append (cons a as') bs) cs = append (cons a as') (append bs cs)
      by
      intro a as' h
      repeat rw [cons_append]
      rw [h] )

def length : List α → Nat
| nil => .zero
| cons _ as => as.length.succ

example {as bs : List α} : length (append as bs) = .add (length as) (length bs) :=
  List.recOn
    (motive := λ as ↦ (append as bs).length = .add as.length bs.length)
    as
    ( show (append nil bs).length = .add nil.length bs.length by
      rw [nil_append]
      rw [length]
      show bs.length = Nat.zero + bs.length
      rw [Nat.zero_add] )
    ( show (a : α) → (as' : List α) →
        (append as' bs).length = .add as'.length bs.length →
        (append (cons a as') bs).length = .add (cons a as').length bs.length
      by
      intro a as' h
      rw [cons_append]
      repeat rw [length]
      show (append as' bs).length.succ = as'.length.succ + bs.length
      rw [Nat.succ_add]
      show (append as' bs).length.succ = (Nat.add as'.length bs.length).succ
      rw [h] )

end List

inductive BinaryTree
| leaf
| node : BinaryTree → BinaryTree → BinaryTree

inductive CBTree
| leaf
| sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree := sup (λ _ ↦ t)
def toCBTree : Nat → CBTree
| .zero => leaf
| .succ n => (toCBTree n).succ
def omega : CBTree := sup toCBTree

end CBTree

end Hidden

end OtherRecursiveDataTypes

/-!
## Section 7.6. Tactics for Inductive Types
-/
section TacticsForInductiveTypes
end TacticsForInductiveTypes

/-!
## Section 7.7. Inductive Families
-/
section InductiveFamilies
end InductiveFamilies

/-!
## Section 7.8. Axiomatic Details
-/
section AxiomaticDetails
end AxiomaticDetails

/-!
## Section 7.9. Mutual and Nested Inductive Types
-/
section MutalAndNestedInductiveTypes
end MutalAndNestedInductiveTypes

/-!
## Section 7.10 Exercises
-/
section Exercises
end Exercises

